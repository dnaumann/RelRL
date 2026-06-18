open Annot

(* Shared helpers for the alignment subsystem (auto/rewrites/interactive/align):

     - path <-> string conversions for the rewrite-focus API,
     - pretty-printing wrappers over [Pretty],
     - the relational spec scope/typing machinery used by both the CLI spec
       check (align.ml) and the interactive loop-local check (interactive.ml).

   This module sits below all four of those so the shared bits can live in one
   place without a dependency cycle (interactive.ml cannot depend on align.ml,
   which in turn depends on interactive.ml). *)

(* ---- paths -------------------------------------------------------------- *)

let string_of_path (p : Rewrites.path) : string =
  String.concat "." (List.map string_of_int p)

(* "0.1.2" -> Some [0;1;2] ; "" -> Some [] ; anything non-numeric -> None *)
let parse_path (s : string) : Rewrites.path option =
  try
    Some (String.split_on_char '.' s
          |> List.filter (fun x -> x <> "")
          |> List.map int_of_string)
  with _ -> None

(* ---- pretty-printing wrappers ------------------------------------------- *)

let rformula_to_string rf : string =
  let buf = Buffer.create 128 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_margin fmt 80;
  Pretty.pp_rformula fmt rf;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let exp_to_string e : string =
  let buf = Buffer.create 32 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_margin fmt 80;
  Pretty.pp_exp fmt e;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let varbind_to_string (vb : varbind option) : string = match vb with
  | None -> ""
  | Some vbind ->
    let buf = Buffer.create 16 in
    let fmt = Format.formatter_of_buffer buf in
    Format.pp_set_margin fmt 80;
    Pretty.pp_varbind fmt vbind;
    Format.pp_print_flush fmt ();
    Buffer.contents buf

let param_to_string (p : meth_param_info) : string =
  Printf.sprintf "%s:%s"
    (Astutil.string_of_ident p.param_name.node)
    (string_of_ity p.param_ty)

let effect_to_string eff : string =
  let buf = Buffer.create 128 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_margin fmt 80;
  Pretty.pp_effect fmt eff;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let mk_var_exp id ty : exp t =
  Evar (id -: ty) -: ty

(* ---- relational spec scope ---------------------------------------------- *)

let params_of (d : meth_decl) : (ident * ity) list =
  List.map (fun (p : meth_param_info) -> (p.param_name.node, p.param_ty)) d.params

(* A tenv exposing only [alloc] (from [initial_tenv]), the given parameters, and
   optionally [result], built over [ctbl] so types resolve but module globals
   and locals do not.  Type-checking an rformula against it therefore rejects
   any reference outside the supplied names. *)
let restricted_tenv ctbl params result_opt : Typing.tenv =
  let e = Typing.{ initial_tenv with ctbl } in
  let e = List.fold_left (fun e (x, ty) -> Typing.add_to_ctxt e x ty) e params in
  match result_opt with
  | Some ty -> Typing.add_to_ctxt e (ident "result") ty
  | None -> e

(* Method declarations + parsed/checked CLI relational specs for a method pair,
   shared by the batch exporter (align.ml) and the interactive server
   (interactive.ml).  [spec_pre]/[spec_post] hold the typed -rpre/-rpost when
   they parsed and type-checked; [rpre]/[rpost] keep the raw source. *)
type pair_ctx = {
  ldecl     : meth_decl option;
  rdecl     : meth_decl option;
  spec_pre  : rformula option;
  spec_post : rformula option;
  rpre      : string;
  rpost     : string;
}

(* A CLI spec that was supplied but failed to parse/type-check is an error;
   [[]] means everything supplied is OK. *)
let cli_spec_errors ctx : string list =
  let err name src parsed : string list =
    if String.trim src <> "" && parsed = None
    then [Printf.sprintf "-%s was supplied but failed parse/typecheck" name]
    else [] in
  err "rpre" ctx.rpre ctx.spec_pre @ err "rpost" ctx.rpost ctx.spec_post

(* Parse [src] and check it refers only to the args of [ldecl]/[rdecl] (plus
   [result] when [with_result]).  Out-of-scope references surface as the
   type-checker's "unknown variable" error. *)
let check_rformula ctbl (ldecl : meth_decl) (rdecl : meth_decl) ~with_result src
  : (Typing.T.rformula, string) result =
  match Astutil.parse_rformula_string src with
  | Error msg -> Error ("parse " ^ msg)
  | Ok rf ->
    let lres = if with_result then Some ldecl.result_ty else None in
    let rres = if with_result then Some rdecl.result_ty else None in
    let bienv =
      Typing.{ initial_bi_tenv with
               left_tenv  = restricted_tenv ctbl (params_of ldecl) lres;
               right_tenv = restricted_tenv ctbl (params_of rdecl) rres } in
    Typing.tc_rformula bienv rf
