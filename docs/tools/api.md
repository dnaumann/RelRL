# Tools API Reference

## tools/main.ml

Command-line interface and entry point.

### Command Line Flags

```ocaml
(* Input/Output *)
val program_files : pathname list ref
val output : out_channel option ref

(* Flags *)
val only_parse_flag : bool ref       (* --parse-only *)
val only_typecheck_flag : bool ref   (* --typecheck-only *)
val debug : bool ref                 (* --debug *)
val no_encap_check : bool ref        (* --no-encap-check *)
val no_frame_lemma : bool ref        (* --no-frame-lemma *)
val locEq_method : string ref        (* --locEq *)
val all_exists_mode : bool ref       (* -all-exists *)

(* Configuration *)
val margin : int ref                 (* Output width *)
```

### Main Functions

```ocaml
val run : unit -> unit

val parse_file : string -> Ast.program list
val parse_program : string list -> Ast.program list

val typecheck_program : Ast.program list -> (penv * Ctbl.t)

val set_output : string -> unit
val close_output : unit -> unit
val get_formatter : unit -> Format.formatter
```
