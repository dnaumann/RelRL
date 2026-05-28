open Annot

(* Interactive alignment session.

   Holds the current bicommand as mutable state behind an HTTP API, so a client
   (browser UI, curl, or an MCP) can repeatedly inspect the alignment, ask which
   rewrites apply where, apply them at a focus, undo, and finally export a
   bimodule skeleton.  All rewriting is delegated to [Rewrites]; the default
   (sequential) alignment is built by [Align.compose_sequentially].

   A relational pre/postcondition may be supplied (CLI -rpre/-rpost); it is
   parsed and checked to refer only to the method arguments (and, for the
   postcondition, [result]).  It then informs the ranking of synthesised loop
   alignment guards (see [/guards]). *)

(* ---- paths -------------------------------------------------------------- *)

let string_of_path (p : Rewrites.path) =
  String.concat "." (List.map string_of_int p)

(* "0.1.2" -> Some [0;1;2] ; "" -> Some [] ; anything non-numeric -> None *)
let parse_path (s : string) : Rewrites.path option =
  try
    Some (String.split_on_char '.' s
          |> List.filter (fun x -> x <> "")
          |> List.map int_of_string)
  with _ -> None

(* Every node position in the tree, root ([]) first, in preorder. *)
let rec all_paths (cc : bicommand) : Rewrites.path list =
  let n = Rewrites.child_count cc in
  [] :: List.concat
          (List.init n
             (fun i ->
                List.map (fun p -> i :: p)
                  (all_paths (Rewrites.get_child cc i))))

(* ---- JSON rendering ----------------------------------------------------- *)

let suggestions_at current p =
  List.map (fun (name, cc) -> (p, name, cc)) (Rewrites.suggest_at p current)

let suggestions_all current =
  List.concat (List.map (suggestions_at current) (all_paths current))

let json_of_suggestions (suggs : (Rewrites.path * string * bicommand) list) =
  `List (List.map (fun (p, name, cc) ->
      `Assoc [ "path",   `String (string_of_path p);
               "rule",   `String name;
               "result", `String (Align.bicommand_to_string cc) ])
      suggs)
  |> Yojson.Safe.to_string

(* ---- relational spec: parse + scope/type-check -------------------------- *)

let rformula_to_string rf =
  let buf = Buffer.create 128 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_margin fmt 80;
  Pretty.pp_rformula fmt rf;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

(* A tenv exposing only [alloc] (from [initial_tenv]), the given parameters, and
   optionally [result], built over [ctbl] so types resolve but module globals
   and locals do not.  Type-checking an rformula against it therefore rejects
   any reference outside the method args (+ result). *)
let restricted_tenv ctbl params result_opt =
  let e = Typing.{ initial_tenv with ctbl } in
  let e = List.fold_left (fun e (x, ty) -> Typing.add_to_ctxt e x ty) e params in
  match result_opt with
  | Some ty -> Typing.add_to_ctxt e (ident "result") ty
  | None -> e

let params_of (d : meth_decl) =
  List.map (fun (p : meth_param_info) -> (p.param_name.node, p.param_ty)) d.params

(* Parse [src] and check it refers only to the args of [ldecl]/[rdecl] (plus
   [result] when [with_result]).  Out-of-scope references surface as the
   type-checker's "unknown variable" error. *)
let check_rformula ctbl (ldecl : meth_decl) (rdecl : meth_decl) ~with_result src =
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

(* Variables the spec forces to agree: those under an [Agree]/[=:=] atom (and
   conjunctions / quantifiers / lets thereof).  Used to rank guard candidates. *)
let rec agreed_vars rf =
  match rf with
  | Rbiequal (e1, e2) when e1 = e2 -> free_vars_exp e1
  | Ragree (e, _) -> free_vars_exp e
  | Rconn (Ast.Conj, a, b) -> IdS.union (agreed_vars a) (agreed_vars b)
  | Rquant (_, _, r) | Rlater r -> agreed_vars r
  | Rlet (_, _, r) -> agreed_vars r
  | _ -> IdS.empty

let guard_rationale = function
  | "lockstep"    -> "iterate both loops together (one body per joint step)"
  | "diff"        -> "lockstep while both guards hold, then drain the loop still running"
  | "left-first"  -> "run the left loop to completion, then the right"
  | "right-first" -> "run the right loop to completion, then the left"
  | _             -> ""

(* ---- export ------------------------------------------------------------- *)

let param_to_string (p : meth_param_info) =
  Printf.sprintf "%s:%s"
    (Astutil.string_of_ident p.param_name.node)
    (string_of_ity p.param_ty)

let mk_var_exp id ty =
  Evar (id -: ty) -: ty

let param_agreements (ld : meth_decl) (rd : meth_decl) : rformula list =
  let right_params =
    List.map
      (fun p -> (Astutil.string_of_ident p.param_name.node, p.param_ty))
      rd.params
  in
  ld.params
  |> List.filter_map (fun lp ->
       let name = Astutil.string_of_ident lp.param_name.node in
       match List.assoc_opt name right_params with
       | Some rty when rty = lp.param_ty ->
         let e = mk_var_exp lp.param_name.node lp.param_ty in
         Some (Rbiequal (e, e))
       | _ -> None)

let result_agreement (ld : meth_decl) (rd : meth_decl) : rformula list =
  if ld.result_ty = rd.result_ty then
    let e = mk_var_exp (ident "result") ld.result_ty in
    [Rbiequal (e, e)]
  else []

let default_pre_specs (ld : meth_decl) (rd : meth_decl) : rformula list =
  let lpre = List.map (fun f -> Rleft f) (spec_preconds ld.meth_spec) in
  let rpre = List.map (fun f -> Rright f) (spec_preconds rd.meth_spec) in
  lpre @ rpre @ param_agreements ld rd

let default_post_specs (ld : meth_decl) (rd : meth_decl) : rformula list =
  let lpost = List.map (fun f -> Rleft f) (spec_postconds ld.meth_spec) in
  let rpost = List.map (fun f -> Rright f) (spec_postconds rd.meth_spec) in
  lpost @ rpost @ result_agreement ld rd

(* A .rl skeleton for the current alignment.  Includes concrete method
   parameters/results and relational specs (CLI-provided -rpre/-rpost when
   present, otherwise relational defaults derived from unary specs). *)
let bimodule_skeleton lmod lmeth rmod rmeth bicom_str ldecl rdecl spec_pre spec_post rpre_src rpost_src =
  let buf = Buffer.create 1024 in
  let p fmt = Printf.bprintf buf fmt in
  let write_rel_clause kind rf =
    p "    %s { %s }\n" kind (rformula_to_string rf)
  in
  let write_cli_clause kind src =
    p "    %s { %s }\n" kind src
  in
  p "/* Alignment skeleton generated by `whyrel -align -i`.\n";
  p "   left  = %s.%s   right = %s.%s\n" lmod lmeth rmod rmeth;
  p "   TODO: declare the biinterface and review exported specs. */\n\n";
  p "bimodule %s_%s_REL (%s | %s) =\n\n" lmod rmod lmod rmod;
  (match ldecl, rdecl with
   | Some (ld : meth_decl), Some (rd : meth_decl) ->
     let lparams = String.concat ", " (List.map param_to_string ld.params) in
     let rparams = String.concat ", " (List.map param_to_string rd.params) in
     p "  meth %s (%s|%s) : (%s|%s)\n"
       lmeth lparams rparams (string_of_ity ld.result_ty) (string_of_ity rd.result_ty);
     let cli_pre = String.trim rpre_src in
     let cli_post = String.trim rpost_src in
     (if cli_pre <> "" then write_cli_clause "requires" cli_pre
      else
        let pre_specs =
          match spec_pre with
          | Some rf -> [rf]
          | None -> default_pre_specs ld rd
        in
        if pre_specs = [] then p "    requires { Both (true) }\n"
        else List.iter (write_rel_clause "requires") pre_specs);
     (if cli_post <> "" then write_cli_clause "ensures" cli_post
      else
        let post_specs =
          match spec_post with
          | Some rf -> [rf]
          | None -> default_post_specs ld rd
        in
        if post_specs = [] then p "    ensures { Both (true) }\n"
        else List.iter (write_rel_clause "ensures") post_specs)
   | _ ->
     p "  meth %s ( (* left params *) | (* right params *) ) : ( unit | unit )\n" lmeth;
     let cli_pre = String.trim rpre_src in
     let cli_post = String.trim rpost_src in
     if cli_pre <> "" then write_cli_clause "requires" cli_pre
     else p "    requires { Both (true) }\n";
     if cli_post <> "" then write_cli_clause "ensures" cli_post
     else p "    ensures { Both (true) }\n");
  p "  =\n";
  List.iter (fun l -> p "    %s\n" l) (String.split_on_char '\n' bicom_str);
  p "  ;\n\nend\n";
  Buffer.contents buf

(* ---- session ------------------------------------------------------------ *)

let text = "text/plain; charset=utf-8"
let json = "application/json"

(* Build the default (sequential) alignment for the named method pair and serve
   it behind the rewriting API on [port].  [rpre]/[rpost] are the (possibly
   empty) relational pre/postcondition source strings. *)
let run penv ctbl lmod lmeth rmod rmeth output_file rpre rpost port =
  let base    = Align.compose_sequentially penv lmod lmeth rmod rmeth in
  let current = ref base in
  let history = ref [] in     (* most-recent-first stack of prior states *)
  let future  = ref [] in     (* most-recent-first stack of undone states *)
  let mcp_undo_rule = "undo" in
  let mcp_redo_rule = "redo" in

  let find_interface_decl mdl_name meth_name =
    match M.find_opt (Id mdl_name) penv with
    | Some (Unary_module mdl) ->
      (match M.find_opt mdl.mdl_interface penv with
       | Some (Unary_interface intr) ->
         List.find_map (function
           | Intr_mdecl d when d.meth_name.node = Id meth_name -> Some d
           | _ -> None) intr.intr_elts
       | _ -> None)
    | _ -> None
  in
  let enrich_decl mdl_name meth_name dopt =
    match dopt with
    | None -> find_interface_decl mdl_name meth_name
    | Some d ->
      if d.meth_spec <> [] then Some d
      else
        (match find_interface_decl mdl_name meth_name with
         | Some idecl -> Some { d with meth_spec = idecl.meth_spec }
         | None -> Some d)
  in
  let ldecl = enrich_decl lmod lmeth (Align.find_method_decl penv lmod lmeth) in
  let rdecl = enrich_decl rmod rmeth (Align.find_method_decl penv rmod rmeth) in

  (* Parse + check the relational spec against the two method signatures. *)
  let spec_pre, spec_post =
    match ldecl, rdecl with
    | Some ld, Some rd ->
      let chk label ~with_result src =
        if src = "" then None
        else match check_rformula ctbl ld rd ~with_result src with
          | Ok rf -> Printf.printf "[align] %s: OK\n%!" label; Some rf
          | Error msg -> Printf.printf "[align] %s: REJECTED -- %s\n%!" label msg; None
      in
      (chk "relational precondition (-rpre)" ~with_result:false rpre,
       chk "relational postcondition (-rpost)" ~with_result:true rpost)
    | _ ->
      if rpre <> "" || rpost <> "" then
        Printf.printf "[align] warning: method declarations not found; spec unchecked\n%!";
      (None, None)
  in
  let cli_pre_supplied = String.trim rpre <> "" in
  let cli_post_supplied = String.trim rpost <> "" in
  let cli_pre_ok = (not cli_pre_supplied) || spec_pre <> None in
  let cli_post_ok = (not cli_post_supplied) || spec_post <> None in
  let export_error () =
    let errs =
      (if cli_pre_supplied && not cli_pre_ok
       then ["-rpre was supplied but failed parse/typecheck"] else [])
      @
      (if cli_post_supplied && not cli_post_ok
       then ["-rpost was supplied but failed parse/typecheck"] else [])
    in
    String.concat "; " errs
  in
  (* Variables the spec forces to agree, across pre and post. *)
  let agreed =
    List.fold_left
      (fun acc -> function Some rf -> IdS.union acc (agreed_vars rf) | None -> acc)
      IdS.empty [spec_pre; spec_post]
  in

  let serialize () = Align.bicommand_to_string !current in
  let snapshot () =
    history := !current :: !history;
    future := []
  in

  (* The guard candidate recommended for a loop pair.  Identical guards are the
     dominant signal that the two loops run the same number of times, so lockstep
     is recommended (this covers aligning a method against itself).  When the
     guards differ, lockstep is only recommended if the spec forces every guard
     variable to agree (making them equivalent); otherwise the data-dependent
     diff alignment, which drains whichever loop outlasts the other. *)
  let recommend = function
    | Bisplit (While (le, _, _), While (re, _, _)) ->
      if le = re then "lockstep"
      else
        let vs = IdS.union (free_vars_exp le) (free_vars_exp re) in
        if not (IdS.is_empty agreed) && IdS.subset vs agreed then "lockstep"
        else "diff"
    | _ -> "diff"
  in

  (* Resolve a rule name (+ optional [guard]/[inv] query params at path [p]) to a
     (label, rewrite).  [weave_while] takes a synthesised guard; [add_invariant]
     takes the index of a coupling candidate; the rest come from the registry. *)
  let resolve name get p =
    let assoc () =
      match List.assoc_opt name Rewrites.all_rewrites with
      | Some r -> Some (name, r) | None -> None
    in
    match name with
    | "weave_while" ->
      (match get "guard" with
       | None -> assoc ()
       | Some g ->
         (match Rewrites.subterm_at p !current with
          | None -> None
          | Some sub ->
            (match List.assoc_opt g (Rewrites.guard_candidates sub) with
             | Some ag -> Some (name ^ "[" ^ g ^ "]", Rewrites.weave_while_guard ag)
             | None -> None)))
    | "add_invariant" ->
      (match get "inv", Rewrites.subterm_at p !current with
       | Some k, Some sub ->
         (match int_of_string_opt k with
          | Some i ->
            let cs = Rewrites.coupling_candidates sub in
            if i >= 0 && i < List.length cs
            then Some (Printf.sprintf "add_invariant[%d]" i,
                       Rewrites.add_invariant (List.nth cs i))
            else None
          | None -> None)
       | _ -> None)
    | _ -> assoc ()
  in
  let apply_rewrite label r p =
    match Rewrites.apply_at p r !current with
    | Some cc' -> snapshot (); current := cc'; Ok ()
    | None ->
      Error (Printf.sprintf "%s not applicable at path [%s]" label (string_of_path p))
  in

  (* The relational typing context at loop focus [p]: method params + result +
     the locals in scope there.  Lets an MCP-supplied invariant referring to loop
     variables be type-checked. *)
  let loop_tenv p =
    match ldecl, rdecl with
    | Some ld, Some rd ->
      let (lvars, rvars) = Rewrites.scope_at p !current in
      let vb (id, _, ty) = (id.node, ty) in
      Some (Typing.{ initial_bi_tenv with
              left_tenv  =
                restricted_tenv ctbl (params_of ld @ List.map vb lvars) (Some ld.result_ty);
              right_tenv =
                restricted_tenv ctbl (params_of rd @ List.map vb rvars) (Some rd.result_ty) })
    | _ -> None
  in
  (* Parse, type-check in the loop's local scope, and add an MCP-supplied
     relational invariant at loop focus [p]. *)
  let add_mcp_invariant p src =
    match loop_tenv p with
    | None -> Error "method declarations not found"
    | Some bienv ->
      (match Astutil.parse_rformula_string src with
       | Error e -> Error ("parse " ^ e)
       | Ok rf ->
         (match Typing.tc_rformula bienv rf with
          | Error e -> Error e
          | Ok trf ->
            (match Rewrites.apply_at p (Rewrites.add_invariant trf) !current with
             | Some cc' -> snapshot (); current := cc'; Ok ()
             | None -> Error "focus is not a loop (weave the loop first)")))
  in
  let do_undo () =
    match !history with
    | [] -> Error "nothing to undo"
    | prev :: rest ->
      future := !current :: !future;
      current := prev;
      history := rest;
      Ok ()
  in
  let do_redo () =
    match !future with
    | [] -> Error "nothing to redo"
    | next :: rest ->
      history := !current :: !history;
      current := next;
      future := rest;
      Ok ()
  in
  (* Undo/redo are rewrite history only: non-rewrite commands clear both stacks. *)
  let clear_history () = history := []; future := [] in
  let do_auto ()  = current := Rewrites.auto_align !current; clear_history () in
  let do_reset () = current := base; clear_history () in
  let history_json () =
    Yojson.Safe.to_string
      (`Assoc [ "undo_available", `Bool (!history <> []);
                "redo_available", `Bool (!future <> []);
                "undo_depth",     `Int (List.length !history);
                "redo_depth",     `Int (List.length !future) ])
  in

  let show_spec () =
    let line label = function
      | None -> label ^ ": (none)"
      | Some rf -> label ^ ": " ^ rformula_to_string rf
    in
    String.concat "\n" [ line "requires" spec_pre; line "ensures" spec_post; "" ]
  in

  (* Synthesised loop alignments at focus [p], ranked using the spec. *)
  let guards_at p =
    match Rewrites.subterm_at p !current with
    | None -> Yojson.Safe.to_string (`Assoc ["error", `String "no subterm at path"])
    | Some sub ->
      match Rewrites.guard_candidates sub with
      | [] -> Yojson.Safe.to_string
                (`Assoc ["error",
                         `String "focus is not a loop pair (Bisplit(while,while))"])
      | cands ->
        let best = recommend sub in
        `List (List.map (fun (name, ag) ->
            let result = match Rewrites.apply_at p (Rewrites.weave_while_guard ag) !current with
              | Some cc' -> Align.bicommand_to_string cc'
              | None -> "(n/a)" in
            `Assoc [ "guard",       `String name;
                     "recommended", `Bool (name = best);
                     "rationale",   `String (guard_rationale name);
                     "result",      `String result ])
            cands)
        |> Yojson.Safe.to_string
  in

  (* Relational invariants for a loop focus [p]: those already carried on the
     loop (lifted from the unary loops by [weave_while]), plus agreement coupling
     candidates (v =:= v) to consider adding. *)
  let invariants_at p =
    match Rewrites.subterm_at p !current with
    | None -> Yojson.Safe.to_string (`Assoc ["error", `String "no subterm at path"])
    | Some sub ->
      let carried = match sub with
        | Biwhile (_, _, _, spec, _) -> spec.biwinvariants
        | _ -> [] in
      let cands = Rewrites.coupling_candidates sub in
      if carried = [] && cands = [] then
        Yojson.Safe.to_string (`Assoc ["error", `String "focus is not a loop"])
      else
        `Assoc [
          "carried_invariants",
            `List (List.map (fun rf -> `String (rformula_to_string rf)) carried);
          "coupling_candidates",
            `List (List.mapi (fun i rf ->
                `Assoc ["index", `Int i;
                        "invariant", `String (rformula_to_string rf)]) cands);
          "note", `String
            "carried_invariants are already on the loop; add a coupling candidate \
             with POST /rewrite?rule=add_invariant&inv=<index>&path=<P>" ]
        |> Yojson.Safe.to_string
  in

  let help =
    String.concat "\n"
      [ "WhyRel interactive alignment server.";
        "";
        "  GET  /                        this help";
        "  GET  /ui                      browser UI (interactive rewrites)";
        "  GET  /bicom                   current alignment (text)";
        "  GET  /bicom.html              current alignment (HTML)";
        "  GET  /spec                    relational pre/postcondition";
        "  GET  /history                 undo/redo availability and stack depths (JSON)";
        "  GET  /rules                   names of all rewrite rules (JSON)";
        "  GET  /suggest                 every applicable rewrite, all foci (JSON)";
        "  GET  /suggest?path=0.1        applicable rewrites at one focus (JSON)";
        "  GET  /guards?path=P           synthesised loop alignments at focus P,";
        "                                ranked by the spec (JSON)";
        "  GET  /invariants?path=P       carried invariants + coupling candidates";
        "                                for a loop focus (JSON)";
        "  POST /rewrite?rule=R&path=P   apply rule R at focus P (path optional)";
        "  POST /rewrite?rule=undo       undo the most recent change";
        "  POST /rewrite?rule=redo       redo the most recently undone change";
        "  POST /rewrite?rule=weave_while&guard=G&path=P   weave a loop with a";
        "                                synthesised guard G (see /guards)";
        "  POST /rewrite?rule=add_invariant&inv=K&path=P   add coupling candidate K";
        "                                (from /invariants) to the loop at P";
        "  POST /rewrite?rule=add_invariant&formula=R&path=P   add a (caller/MCP-)";
        "                                supplied relational invariant R, type-checked";
        "                                in the loop's local scope";
        "  POST /undo                    revert the last change";
        "  POST /redo                    re-apply the last undone change";
        "  POST /auto                    greedily weave toward lockstep";
        "  POST /reset                   back to the sequential default";
        "  POST /export                  write a .rl bimodule skeleton to the";
        "                                output file (" ^ output_file ^ ")";
        "";
        "A path is a dot-separated list of child indices (e.g. 0.1); empty = root.";
        "" ]
  in

  let handler ~meth ~path ~query =
    ignore meth;
    let params = Http_server.query_params query in
    let get k = List.assoc_opt k params in
    match path with
    | "/" | "/help"  -> (200, text, help)
    | "/ui" ->
      (200, "text/html; charset=utf-8",
       Html_server.build_interactive_html lmod lmeth rmod rmeth)
    | "/bicom"       -> (200, text, serialize ())
    | "/spec"        -> (200, text, show_spec ())
    | "/history"     -> (200, json, history_json ())
    | "/bicom.html"  ->
      (200, "text/html; charset=utf-8",
       Html_server.build_html lmod lmeth rmod rmeth (serialize ()))
    | "/rules" ->
      let rules = List.map fst Rewrites.all_rewrites @ [mcp_undo_rule; mcp_redo_rule] in
      let j = `List (List.map (fun n -> `String n) rules) in
      (200, json, Yojson.Safe.to_string j)
    | "/suggest" ->
      (match get "path" with
       | None   -> (200, json, json_of_suggestions (suggestions_all !current))
       | Some s ->
         (match parse_path s with
          | None   -> (400, text, "bad path: " ^ s)
          | Some p -> (200, json, json_of_suggestions (suggestions_at !current p))))
    | "/guards" ->
      (match get "path" with
       | None   -> (400, text, "give ?path=P pointing at a loop pair")
       | Some s ->
         (match parse_path s with
          | None   -> (400, text, "bad path: " ^ s)
          | Some p -> (200, json, guards_at p)))
    | "/invariants" ->
      (match get "path" with
       | None   -> (400, text, "give ?path=P pointing at a loop")
       | Some s ->
         (match parse_path s with
          | None   -> (400, text, "bad path: " ^ s)
          | Some p -> (200, json, invariants_at p)))
    | "/rewrite" ->
      (match get "rule" with
       | None -> (400, text, "missing 'rule' parameter")
       | Some name when name = mcp_undo_rule ->
         (match do_undo () with
          | Ok ()   -> (200, text, serialize ())
          | Error m -> (409, text, m))
       | Some name when name = mcp_redo_rule ->
         (match do_redo () with
          | Ok ()   -> (200, text, serialize ())
          | Error m -> (409, text, m))
       | Some "add_invariant" when get "formula" <> None ->
         let s = match get "path" with Some s -> s | None -> "" in
         let f = match get "formula" with Some f -> f | None -> "" in
         (match parse_path s with
          | None   -> (400, text, "bad path: " ^ s)
          | Some p ->
            (match add_mcp_invariant p f with
             | Ok ()   -> (200, text, serialize ())
             | Error m -> (400, text, m)))
       | Some name ->
         let s = match get "path" with Some s -> s | None -> "" in
         (match parse_path s with
          | None   -> (400, text, "bad path: " ^ s)
          | Some p ->
            (match resolve name get p with
             | None -> (400, text, Printf.sprintf "unknown rule/guard: %s" name)
             | Some (label, r) ->
               (match apply_rewrite label r p with
                | Ok ()    -> (200, text, serialize ())
                | Error m  -> (409, text, m)))))
    | "/undo" ->
      (match do_undo () with
       | Ok ()   -> (200, text, serialize ())
       | Error m -> (409, text, m))
    | "/redo" ->
      (match do_redo () with
       | Ok ()   -> (200, text, serialize ())
       | Error m -> (409, text, m))
    | "/auto"  -> do_auto ();  (200, text, serialize ())
    | "/reset" -> do_reset (); (200, text, serialize ())
    | "/export" ->
      if cli_pre_ok && cli_post_ok then
        let skel =
          bimodule_skeleton lmod lmeth rmod rmeth (serialize ())
            ldecl rdecl spec_pre spec_post rpre rpost
        in
        let oc = open_out output_file in
        output_string oc skel;
        close_out oc;
        (200, text, Printf.sprintf "bimodule skeleton written to %s\n" output_file)
      else
        (400, text, "export blocked: " ^ export_error () ^ "\n")
    | _ -> (404, json, {|{"error":"not found"}|})
  in
  Lwt_main.run (Http_server.start_dispatch_server handler port)
