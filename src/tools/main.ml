open Ast
open Astutil
open Annot
open Lib
open Ctbl
open Typing
open Translate
open Align

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

let align_mode = ref false
let align_interactive_mode = ref false
let align_port = ref 8080
let align_rpre  : string ref = ref ""
let align_rpost : string ref = ref ""

let align_left_module   : string ref = ref ""
let align_left_method : string ref = ref ""
let align_right_module  : string ref = ref ""
let align_right_method: string ref = ref ""

let output : out_channel option ref = ref None

let locEq_method : string ref = ref ""

let margin : int ref = ref 80

let output_fname : string ref = ref ""

let set_output fname = output_fname := fname; output := Some (open_out fname)


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

   "-o", String set_output,
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

   "-align", Set align_mode,
   " Transforms a given pair of unary programs into an aligned biprogram;
     Expects the following format: whyrel -align -l <module> <method> -r <module> <method> files -o <file>";

   "-l", Tuple [Set_string align_left_module; Set_string align_left_method],
   "<module> <method>  Left-hand side module and method for alignment";

   "-r", Tuple [Set_string align_right_module; Set_string align_right_method],
   "<module> <method>  Right-hand side module and method for alignment";

   "-i", Set align_interactive_mode,
   " In align mode: start the interactive rewriting server (stateful; serves /suggest, /rewrite, /undo, /export)";

   "-port", Set_int align_port,
   "<n>  In align mode: serve on port <n> (default 8080)";

   "-rpre", Set_string align_rpre,
   "<rformula>  In align mode: relational precondition (may refer to method args)";

   "-rpost", Set_string align_rpost,
   "<rformula>  In align mode: relational postcondition (may refer to method args and result)";
  ]

let set_debug_flags () =
  tc_debug := !debug;
  trans_debug := !debug;
  Rename_locals.pretrans_debug := !debug;
  Encap_check.encap_debug := !debug;
  Pretrans.locEq_debug := !debug

let set_behaviour_flags () =
  Encap_check.do_encap_check := not !no_encap_check;
  Translate.gen_frame_lemma := not !no_frame_lemma;
  Pretrans.simplify_effects := not !no_simplify_effects;
  Pretrans.resolve_for_locEq := not !no_simplify_effects;
  Typing.all_exists_mode := !all_exists_mode;
  Typing.only_parse_or_typecheck := !only_parse_flag || !only_typecheck_flag;
  ()


let usage = "Usage: " ^ get_progname () ^ " [options] [<file>...]"

let close_output () =
  match !output with
  | None -> ()
  | Some out_chan -> close_out out_chan

let get_formatter () =
  match !output with
  | None -> Format.std_formatter
  | Some out_chan -> Format.formatter_of_out_channel out_chan

let parse_program files =
  let progs = concat_map parse_file files in
  let main_interface = no_loc the_main_interface in
  no_loc (Unr_intr main_interface) :: progs

let typecheck_program prog =
  match tc_program prog with
  | Ok (penv, ctbl) -> (penv, ctbl)
  | Error msg -> Printf.fprintf stderr "%s\n" msg; exit 1

let translate_program fmt penv ctbl =
  let emit_mlw mlw =
    Why3.Mlw_printer.pp_mlw_file fmt mlw;
    Format.pp_print_newline fmt ();
    Format.pp_print_newline fmt ();
    Format.print_flush () in
  let ctxt, state_module = Translate.Build_State.mk (penv,ctbl) in
  let mlw_files = compile_penv ctxt penv in
  emit_mlw state_module;
  (* Why3.Mlw_printer.pp_mlw_file Format.std_formatter (Why3.Ptree.mlw_file_of_sexp (Sexplib.Sexp.load_sexp "sexp.txt")); *)
  (* Sexplib.Sexp.output_hum stdout (Sexplib.Sexp.load_sexp "sexp.txt");
  output_char stdout '\n';
  flush stdout; *)
  (* (Sexplib.Sexp.save_sexps_hum "sexp.txt" ((List.map Why3.Ptree.sexp_of_mlw_file) mlw_files)); *)
  List.iter emit_mlw mlw_files

let print_version () = Printf.fprintf stdout "WhyRel, version 0.3\n"

let main () =
  let add_program_file s = program_files := s :: !program_files in
  Arg.parse (Arg.align args) add_program_file usage;
  program_files := List.rev !program_files;
  set_debug_flags ();
  set_behaviour_flags ();
  if !only_print_version then print_version () else
  if List.length !program_files = 0 then 
  Printf.fprintf stderr "Error! No input files specified\n"  else
  let program = parse_program !program_files  in
  if !only_parse_flag then () else
  let penv, ctbl = typecheck_program program in
    (* if !align_mode then Align.align penv ctbl set_output else (); *)
  if !only_typecheck_flag then () else 
  if !locEq_method <> "" then 
      let meth_name = Id !locEq_method in
      let program = filter_out is_relation_module program in
      let penv, ctbl = typecheck_program program in
      Pretrans.handle_local_equivalence meth_name penv ctbl  else
  if !output_fname = "" && !align_mode then
    (let base = Filename.basename (List.hd !program_files) in
     let stem = try Filename.chop_extension base with Invalid_argument _ -> base in
     output_fname := stem ^ "_align_output.rl");
  if !align_mode  
  then 
    if !align_left_module = "" || 
       !align_left_method = "" ||
       !align_right_module = "" ||
       !align_right_method = "" 
    then Printf.fprintf stderr "Error! Expected format: whyrel -align -l <module> <method> -r <module> <method> files [-o <file>]\n" 
    else 
      begin
      Printf.fprintf stdout "penv: \n";
      Format.pp_set_margin Format.std_formatter !margin;
      Pretty.pp_penv Format.std_formatter penv;
      Printf.fprintf stdout "\nctbl: \n";
      Ctbl.debug_print_ctbl stdout ctbl;
      Printf.fprintf stdout "\n%s %s %s %s %s\n"
        !align_left_module !align_left_method
        !align_right_module !align_right_method
        !output_fname;
      if !align_interactive_mode then
        Interactive.run penv ctbl !align_left_module !align_left_method
          !align_right_module !align_right_method !output_fname
          !align_rpre !align_rpost !align_port
      else begin
        let bicom =
          Auto.compose_sequentially penv
            !align_left_module !align_left_method
            !align_right_module !align_right_method
          |> Rewrites.auto_align
        in
        let s = Align.bicommand_to_string bicom in
        print_string s; print_newline ();
        let oc = open_out !output_fname in
        output_string oc s; close_out oc;
        Printf.printf "Written to %s\n%!" !output_fname
      end
      end
  else begin
      let fmt = get_formatter () in
      Format.pp_set_margin fmt !margin;
      let penv = Pretrans.process ctbl penv in
      translate_program fmt penv ctbl
      end;
  
  close_output ()

;;

if not !Sys.interactive
then main ()
else ()
