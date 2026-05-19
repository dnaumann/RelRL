open Ast
open Astutil
open Annot
open Http_server
open Html_server

(* ---- Default Alignment construction --------------------------------------------- *)

(* Find the body of a named method in a named unary module from the typed
   program environment. Returns [None] if the module or method is absent, or
   if the method has no implementation (extern / abstract). *)
let find_method_body (penv: penv) mdl_name meth_name : command option =
  let mdl_id  = Id mdl_name  in
  let meth_id = Id meth_name in
  match M.find_opt mdl_id penv with
  | Some (Unary_module mdl) ->
    (match List.find_opt (function
           | Mdl_mdef (Method (decl, _)) -> decl.meth_name.node = meth_id
           | _ -> false) mdl.mdl_elts with
     | Some (Mdl_mdef (Method (_, body))) -> body
     | _ -> None)
  | _ -> None

let skip = Acommand Skip

(* Flatten top-level Seq nodes; does not pierce Vardecl or other compounds. *)
let rec flatten_seq (c: command) : command list =
  match c with
  | Seq (c1, c2) -> flatten_seq c1 @ flatten_seq c2
  | _ -> [c]

(* Mutually recursive: build_default handles Vardecl/While at the top level;
   interleave_steps handles flat step lists, nesting While pairs as Biwhile. *)
let rec build_default (lc: command) (rc: command) : bicommand =
  match lc, rc with
  | Vardecl (lid, lm, lty, lbody), Vardecl (rid, rm, rty, rbody) ->
    Bivardecl (Some (lid, lm, lty), None,
      Bivardecl (None, Some (rid, rm, rty), build_default lbody rbody))
  | Vardecl (lid, lm, lty, lbody), _ ->
    Bivardecl (Some (lid, lm, lty), None, build_default lbody rc)
  | _, Vardecl (rid, rm, rty, rbody) ->
    Bivardecl (None, Some (rid, rm, rty), build_default lc rbody)
  | _ ->
    mk_biseq (interleave_steps (flatten_seq lc) (flatten_seq rc))

and interleave_steps ls rs =
  match ls, rs with
  | [], [] -> []
  | c :: ls', [] -> Bisplit (c, skip) :: interleave_steps ls' []
  | [], e :: rs' -> Bisplit (skip, e) :: interleave_steps [] rs'
  | c :: ls', e :: rs' ->
    Bisplit (c, skip) :: Bisplit (skip, e) :: interleave_steps ls' rs'

(* Default alignment: interleave left and right method body steps, piercing
   Vardecl nodes with Bivardecl for correct scoping. *)
let compose_sequentially (penv: penv) lmod lmeth rmod rmeth : bicommand =
  match find_method_body penv lmod lmeth, find_method_body penv rmod rmeth with
  | Some lc, Some rc -> build_default lc rc
  | None, _ ->
    Printf.ksprintf failwith
      "compose_sequentially: method body for %s.%s not found" lmod lmeth
  | _, None ->
    Printf.ksprintf failwith
      "compose_sequentially: method body for %s.%s not found" rmod rmeth

(* ---- serialise ------------------------------------------- *)

let bicommand_to_string bicom =
  let buf = Buffer.create 256 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_margin fmt 80;
  Pretty.pp_bicommand fmt bicom;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

(* Build an S-expression describing the default alignment. *)
let build_sexp lmod lmeth rmod rmeth bicom =
  Printf.sprintf "%s\n"
    (bicommand_to_string bicom
     |> String.split_on_char '\n'
     |> List.map (fun l -> "    " ^ l)
     |> String.concat "\n")



(* ---- Entry point --------------------------------------------------------- *)

let run (penv: penv) lmod lmeth rmod rmeth (output_file: string) ~man_mode =
  let default_alignment = compose_sequentially penv lmod lmeth rmod rmeth in
  if man_mode then
    let html = build_html lmod lmeth rmod rmeth (bicommand_to_string default_alignment) in
    Lwt_main.run (start_html_server html 8080)
  else
    let sexp = build_sexp lmod lmeth rmod rmeth default_alignment in
    Lwt_main.run (start_server sexp 8080)
