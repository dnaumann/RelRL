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
