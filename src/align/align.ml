open Annot
open Align_utils

(* Root entry point for alignment.

   Resolves the two method declarations and parses/type-checks the CLI
   relational specs ([-rpre]/[-rpost]) up front, then either serves the
   alignment behind the interactive rewriting HTTP server ([interactive] mode,
   delegated to [Interactive.run]) or, in batch mode, greedily weaves the
   sequential alignment toward lockstep ([Rewrites.auto_align]) and writes a
   full .rl bimodule skeleton ([Interactive.bimodule_skeleton]) to
   [output_file].

   The shared spec scope/typing helpers ([Align_utils.params_of],
   [Align_utils.restricted_tenv], [Align_utils.pair_ctx],
   [Align_utils.check_rformula]) live in [Align_utils] so both this module and
   [Interactive] can use them without a dependency cycle. *)

(* Resolve the method decls (with interface specs merged in) and parse + check
   the CLI relational specs against the two signatures. *)
let resolve_pair_ctx penv ctbl lmod lmeth rmod rmeth rpre rpost : pair_ctx =
  let ldecl = Auto.enrich_decl penv lmod lmeth (find_method_decl penv lmod lmeth) in
  let rdecl = Auto.enrich_decl penv rmod rmeth (find_method_decl penv rmod rmeth) in
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
  { ldecl; rdecl; spec_pre; spec_post; rpre; rpost }

let run penv ctbl program_files lmod lmeth rmod rmeth output_file
    rpre rpost port ~interactive : unit =
  let ctx = resolve_pair_ctx penv ctbl lmod lmeth rmod rmeth rpre rpost in
  if interactive then
    Interactive.run penv ctbl program_files lmod lmeth rmod rmeth output_file
      ctx port
  else
    match cli_spec_errors ctx with
    | _ :: _ as errs ->
      Printf.eprintf "align: export blocked: %s\n%!" (String.concat "; " errs)
    | [] ->
      let bicom =
        Auto.compose_sequentially penv lmod lmeth rmod rmeth
        |> Rewrites.auto_align
      in
      let skel =
        Interactive.bimodule_skeleton lmod lmeth rmod rmeth
          (Pretty.bicommand_to_string bicom)
          ctx.ldecl ctx.rdecl ctx.spec_pre ctx.spec_post ctx.rpre ctx.rpost
      in
      print_string skel; print_newline ();
      let oc = open_out output_file in
      output_string oc skel; close_out oc;
      Printf.printf "Written to %s\n%!" output_file
