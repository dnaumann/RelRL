open Ast
open Astutil
open Annot
open Lib
open Ctbl
open Typing
open Translate

type pathname = string

let program_files : pathname list ref = ref []

let only_parse_flag      = ref false
let only_typecheck_flag  = ref false
let debug                = ref false
let only_print_version   = ref false
let no_encap_check       = ref false
let no_frame_lemma       = ref false
let no_resolve_for_locEq = ref false
let no_simplify_effects  = ref false
let all_exists_mode      = ref false

let output : out_channel option ref = ref None

let locEq_method : string ref = ref ""

let margin : int ref = ref 136

let set_output fname = output := Some (open_out fname)

let close_output () =
  match !output with
  | None -> ()
  | Some out_chan -> close_out out_chan

let get_formatter () =
  match !output with
  | None -> Format.std_formatter
  | Some out_chan -> Format.formatter_of_out_channel out_chan

let print_position outx (lexbuf: Lexing.lexbuf) =
  let pos = lexbuf.lex_curr_p in
  let file,lnum,loc = pos.pos_fname,pos.pos_lnum,pos.pos_cnum - pos.pos_bol in
  Printf.fprintf outx "%s:%d:%d" file lnum loc

let parse_with_error lexbuf =
  try Parser.top Lexer.token lexbuf with
  | Lexer.Lexer_error msg ->
    Printf.fprintf stderr "%a: %s\n" print_position lexbuf msg;
    exit 1
  | Parser.Error ->
    Printf.fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit 1

let parse_file filename =
  let contents = read_file filename in
  let lexbuf = Lexing.from_string ~with_positions:true contents in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_with_error lexbuf

let parse_and_type_check filename =
  let program = parse_file filename in
  match tc_program program with
  | Ok _ -> ()
  | Error msg -> Printf.fprintf stderr "%s\n" msg

let parse_program files =
  let progs = concat_map parse_file files in
  let main_interface = no_loc the_main_interface in
  no_loc (Unr_intr main_interface) :: progs

let translate_program fmt penv ctbl =
  let emit_mlw mlw =
    Why3.Mlw_printer.pp_mlw_file fmt mlw;
    Format.pp_print_newline fmt ();
    Format.pp_print_newline fmt ();
    Format.print_flush () in
  let ctxt, state_module = Translate.Build_State.mk (penv,ctbl) in
  let mlw_files = compile_penv ctxt penv in
  emit_mlw state_module;
  (* (Sexplib.Sexp.save_sexps_hum "sexp.txt" ((List.map Why3.Ptree.sexp_of_mlw_file) mlw_files)); *)
  List.iter emit_mlw mlw_files

let typecheck_program prog =
  match tc_program prog with
  | Ok (penv, ctbl) -> (penv, ctbl)
  | Error msg -> Printf.fprintf stderr "%s\n" msg; exit 1

let run () =
  let program = parse_program !program_files in
  if !only_parse_flag then () else
    let penv, ctbl = typecheck_program program in
    if !only_typecheck_flag then () else begin
      let fmt = get_formatter () in
      Format.pp_set_margin fmt !margin;
      let penv = Pretrans.process ctbl penv in
      translate_program fmt penv ctbl
    end

let rec handle_local_equivalence meth_name =
  let meth_name = Id meth_name in
  let fmt = Format.std_formatter in
  let program = parse_program !program_files in
  let program = filter_out is_relation_module program in
  if !only_parse_flag then () else
    let penv, ctbl = typecheck_program program in
    if !only_typecheck_flag then () else begin
      run_local_equivalence fmt meth_name ctbl penv
    end

and run_local_equivalence fmt meth_name ctbl penv =
  let open Pretrans in
  let penv = Expand_method_spec.expand penv in
  let penv =
    if not !no_resolve_for_locEq then Resolve_datagroups.resolve (ctbl,penv)
    else penv in
  let penv = Normalize_effects.normalize penv in
  Boundary_info.run penv;
  if !debug then begin
      let rec print_boundaries = function
        | [] -> ()
        | (mdl, bnd) :: bnds ->
          Format.printf "Boundary: %a: %a\n"
            Pretty.pp_ident mdl Pretty.pp_effect (eff_of_bnd bnd);
          print_boundaries bnds in
      let boundaries =
        let f mdl a b = (mdl, Boundary_info.overall_boundary mdl) :: b in
        M.fold f penv [] in
      print_boundaries boundaries;
    end;
  try
    LocEq.pp_derive_locEq ~resolve:(not !no_resolve_for_locEq)
      ctbl penv meth_name fmt;
    Format.pp_force_newline fmt ();
    Format.pp_print_flush fmt ()
  with
    LocEq.Unknown_method m ->
    Printf.fprintf stderr "Unknown method %s\n" m;
    exit 1

let print_version () = Printf.fprintf stdout "WhyRel, version 0.2\n"

let args =
  let open Arg in
  ["-parse", Set only_parse_flag,
   " Parse program and exit";

   "-type-check", Set only_typecheck_flag,
   " Type check program and exit";

   "-all-exists", Set all_exists_mode,
   " Intepret relational specs as forall-exists";

   "-debug", Set debug,
   " Print debug information";

   "-o", String (fun f -> set_output f),
   "<file>  Set output file name to <file>";

   "-margin", Set_int margin,
   "<n>  Set printer max columns to <n>";

   "-locEq", Set_string locEq_method,
   "<meth>  Derive the local equivalence spec for method <meth>";

   "-no-simplify-effects", Set no_simplify_effects,
   " Do not attempt to simplify effects";

   "-no-encap", Set no_encap_check,
   " Do not perform the Encap check";

   "-no-frame", Set no_frame_lemma,
   " Do not generate frame lemmas for invariants and couplings";

   "-no-resolve", Set no_resolve_for_locEq,
   " Do not expand \"any\" when generating locEq specs with -locEq";

   "-version", Set only_print_version,
   " Print version";
  ]

let usage = "Usage: " ^ get_progname () ^ " [options] [<file>...]"

let set_debug_flags () =
  tc_debug := !debug;
  trans_debug := !debug;
  Pretrans.pretrans_debug := !debug;
  Encap_check.encap_debug := !debug

let set_behaviour_flags () =
  Encap_check.do_encap_check := not !no_encap_check;
  Translate.gen_frame_lemma := not !no_frame_lemma;
  Pretrans.simplify_effects := not !no_simplify_effects;
  Typing.all_exists_mode := !all_exists_mode;
  ()

let main () =
  let add_program_file s = program_files := s :: !program_files in
  Arg.parse (Arg.align args) add_program_file usage;
  program_files := List.rev !program_files;
  set_debug_flags ();
  set_behaviour_flags ();
  if !only_print_version then print_version () else
  if List.length !program_files = 0 then () else
  if !locEq_method <> "" then handle_local_equivalence !locEq_method
  else run (); close_output ()

;;

if not !Sys.interactive
then main ()
else ()
