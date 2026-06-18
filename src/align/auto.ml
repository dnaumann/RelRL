open Ast
open Annot

(* Leading Vardecl nodes are lifted to Bivardecl so the two sides share
  bimeth scope and the remaining bodies become a single Bisplit (lc, rc).
. *)
let compose_sequentially (penv : penv) lmod lmeth rmod rmeth : bicommand =
	let rec build (lc : command) (rc : command) : bicommand =
		match lc, rc with
		| Vardecl (lid, lm, lty, lbody), Vardecl (rid, rm, rty, rbody) ->
			Bivardecl (Some (lid, lm, lty), None,
				Bivardecl (None, Some (rid, rm, rty), build lbody rbody))
		| Vardecl (lid, lm, lty, lbody), _ ->
			Bivardecl (Some (lid, lm, lty), None, build lbody rc)
		| _, Vardecl (rid, rm, rty, rbody) ->
			Bivardecl (None, Some (rid, rm, rty), build lc rbody)
		| _ ->
			Bisplit (lc, rc)
	in
	match Annot.find_method_body penv lmod lmeth, Annot.find_method_body penv rmod rmeth with
	| Some lc, Some rc -> build lc rc
	| None, _ ->
		Printf.ksprintf failwith
			"compose_sequentially: method body for %s.%s not found" lmod lmeth
	| _, None ->
		Printf.ksprintf failwith
			"compose_sequentially: method body for %s.%s not found" rmod rmeth

let has_effect_spec sp : bool =
  List.exists (function Effects _ -> true | _ -> false) sp

let merge_method_specs mod_spec intr_spec : spec_elt list =
  if mod_spec = [] then intr_spec
  else if has_effect_spec mod_spec || not (has_effect_spec intr_spec) then mod_spec
  else mod_spec @ List.filter (function Effects _ -> true | _ -> false) intr_spec

(* Resolve a method declaration, preferring the module implementation's decl
   [dopt] but folding in the interface decl's specs (notably its effects clause)
   when the implementation omits them. *)
let enrich_decl penv mdl_name meth_name dopt : meth_decl option =
  match dopt with
  | None -> Annot.find_interface_decl penv mdl_name meth_name
  | Some d ->
    (match Annot.find_interface_decl penv mdl_name meth_name with
     | Some idecl -> Some { d with meth_spec = merge_method_specs d.meth_spec idecl.meth_spec }
     | None -> Some d)
