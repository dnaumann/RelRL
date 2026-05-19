# Typing API Reference

## typing/annot.ml — Core Types

### `penv` — Program Environment

```ocaml
type program_elt =
  | Unary_interface of interface_def   (* interface CELL = ... end *)
  | Unary_module    of module_def      (* module ACell : CELL = ... end *)
  | Relation_module of bimodule_def    (* bimodule CELL_REL (ACell | BCell) = ... end *)

type penv = program_elt M.t           (* ident → program_elt *)
```

`penv` maps module/interface names (as `Ast.ident`) to their typed definitions. After typechecking, every top-level declaration in the `.rl` file is an entry.

```ocaml
(* Example: look up a bimodule *)
match M.find (Ast.Id "CELL_REL") penv with
| Relation_module bdef -> bdef.bimdl_elts  (* list of coupling, bimeth defs *)
| _ -> failwith "not a bimodule"

(* Iterate over all modules *)
M.iter (fun name elt ->
  match elt with
  | Unary_module mdef -> ...
  | Relation_module bdef -> ...
  | Unary_interface idef -> ...
) penv
```

### `ity` — Intermediate Types

```ocaml
type ity =
  | Tint | Tbool | Trgn | Tunit | Tprop
  | Tclass of ident          (* class Cell *)
  | Tanyclass                (* type of null *)
  | Tmath of ident * ity option   (* math types, e.g. array *)
  | Tmeth of { params: ity list; ret: ity }
  | Tfunc of { params: ity list; ret: ity }
```

### Key AST Types

```ocaml
(* Annotated node: value paired with its ity *)
type 'a t = { ty: ity; node: 'a }
let ( -: ) node ty = { node; ty }   (* constructor *)

type interface_def = { intr_name: ident; intr_elts: interface_elt list }
type module_def    = { mdl_name: ident; mdl_interface: ident; mdl_elts: module_elt list }
type bimodule_def  = { bimdl_name: ident; bimdl_left_impl: ident;
                       bimdl_right_impl: ident; bimdl_elts: bimodule_elt list }

type meth_decl = {
  meth_name: ident t;
  params: meth_param_info list;
  result_ty: ity;
  meth_spec: spec;        (* Precond | Postcond | Effects *)
  ...
}
type meth_def = Method of meth_decl * command option

type bimeth_decl = {
  bimeth_name: ident;
  bimeth_left_params: meth_param_info list;
  bimeth_right_params: meth_param_info list;
  result_ty: ity * ity;
  bimeth_spec: bispec;    (* Biprecond | Bipostcond | Bieffects *)
  ...
}
type bimeth_def = Bimethod of bimeth_decl * bicommand option

type named_rformula = {
  biformula_name: ident;
  body: rformula;
  is_coupling: bool;   (* true → coupling; false → predicate/lemma *)
  ...
}
```

### Utility Functions

```ocaml
val string_of_ity : ity -> string
val id_name : ident -> string          (* extracts string from Ast.Id *)
val spec_preconds  : spec   -> formula list
val spec_postconds : spec   -> formula list
val bispec_preconds : bispec -> rformula list
```

---

## typing/ctbl.ml — Class Table

`Ctbl.t` is `class_info M.t` — a map from class name to its field declarations. Built from class definitions encountered during typechecking.

```ocaml
type class_info = {
  name: classname;
  fields: field_decl list;    (* field_decl = { field_name; field_ty; attribute } *)
}

type t = class_info M.t
```

### Key Functions

```ocaml
val empty : t

(* Field queries *)
val fields      : t -> classname:ident -> (ident * ity) list
val field_type  : t -> field:ident -> ity option
val field_attr  : t -> field:ident -> modifier option
val is_ghost_field : t -> field:ident -> bool

(* Class queries *)
val class_exists      : t -> classname:ident -> bool
val known_class_names : t -> ident list
val is_array_like_class : t -> classname:ident -> bool  (* has length+slots fields *)

(* Build from AST *)
val of_penv : penv -> t

val debug_print_ctbl : out_channel -> t -> unit
```

```ocaml
(* Example: get fields of Cell class *)
Ctbl.fields ctbl ~classname:(Ast.Id "Cell")
(* → [(Id "value", Tint); (Id "rep", Trgn)] *)
```

---

## typing/typing.ml — Typechecking Entry Point

```ocaml
val tc_program : Ast.program list -> (penv * Ctbl.t) Result.t
```

Takes a list of parsed AST programs (one per file), returns a typed `penv` and `ctbl` or an error string.

### Result Monad

All internal functions use `Result.bind` via `let*`:

```ocaml
let ( let* ) = Result.bind

let* (penv, ctbl) = tc_program progs in
(* penv: program_elt M.t *)
(* ctbl: class_info M.t  *)
```
