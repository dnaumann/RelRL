# WhyRel API Reference

## Core Module APIs

This document provides a reference to the main APIs in WhyRel organized by module.

---

## parser/ast.ml

Core abstract syntax tree types for WhyRel language.

### Type System

```ocaml
(* Location tracking *)
type loc = {
  loc_fname: string;    (* Filename *)
  loc_line: int;        (* Line number *)
  loc_range: int * int; (* Character range *)
}

type 'a node = {
  elt: 'a;    (* Actual element *)
  loc: loc    (* Source location *)
}

(* Helpers *)
val dummy_loc : loc
val no_loc : 'a -> 'a node
```

### Identifiers

```ocaml
type ident =
  | Id of string                (* Unqualified: x *)
  | Qualid of string * string list  (* Qualified: M::C::f *)
```

### Types

```ocaml
type ty = Tctor of ident * ty node list

(* Pre-built primitive types *)
val int_ty : ty
val bool_ty : ty
val rgn_ty : ty
val unit_ty : ty
```

### Expressions

```ocaml
type exp =
  | Econst of const_exp node
  | Evar of ident
  | Ebinop of binop * exp node * exp node
  | Eunrop of unrop * exp node
  | Esingleton of exp node
  | Eimage of exp node * ident
  | Esubrgn of exp node * ident
  | Ecall of ident * exp node list

and const_exp =
  | Enull | Eunit | Eint of int | Ebool of bool | Eemptyset

type binop =
  | Plus | Minus | Mult | Div | Mod
  | Equal | Nequal | Leq | Lt | Geq | Gt
  | And | Or
  | Union | Inter | Diff

type unrop = Uminus | Not
```

### Formulas (Specifications)

```ocaml
type formula =
  | Ftrue | Ffalse
  | Fexp of exp node
  | Finit of let_bound_value node
  | Fnot of formula node
  | Fpointsto of ident * ident * exp node
  | Farray_pointsto of ident * exp node * exp node
  | Fsubseteq of exp node * exp node
  | Fdisjoint of exp node * exp node
  | Fmember of exp node * exp node
  | Flet of ident * ty node option * let_bind * formula node
  | Fconn of connective * formula node * formula node
  | Fquant of quantifier * quantifier_bindings * formula node
  | Fold of exp node * let_bound_value node
  | Ftype of exp node * ident list

and connective = Conj | Disj | Imp | Iff
and quantifier = Forall | Exists

type qbind = {
  name: ident;
  ty: ty node;
  in_rgn: exp node option;
  is_non_null: bool;
}
```

### Commands

```ocaml
type atomic_command =
  | Skip
  | Assign of ident * exp node
  | Havoc of ident
  | New_class of ident * ident
  | New_array of ident * ident * exp node
  | Field_deref of ident * ident * ident
  | Field_assign of ident * ident * exp node
  | Array_assign of ident * exp node * exp node
  | (* ... more commands ... *)

type command = atomic_command node list
```

### Declarations

```ocaml
type modifier = Ghost | Public | Modscope

type class_def = {
  class_name: ident;
  fields: field_def list;
  class_rep: ident option;
}

type field_def = {
  field_name: ident;
  field_type: ty node;
  field_mod: modifier;
}

type method_decl = {
  meth_name: ident node;
  meth_params: param_def list;
  meth_return_type: ty node option;
  meth_spec: spec list;
}

type interface_def = {
  intr_name: ident;
  intr_elts: interface_elt list;
}

type module_def = {
  mdl_name: ident;
  mdl_interface: ident;
  mdl_elts: module_elt list;
}

type bimodule_def = {
  bimdl_name: ident;
  bimdl_left_impl: ident;
  bimdl_right_impl: ident;
  bimdl_elts: bimodule_elt list;
}

type program =
  | Unr_intr of interface_def node
  | Mdl of module_def node
  | Bi_intr of biinterface_def node
  | Bi_mdl of bimodule_def node
  | Datagroup of datagroup_def node
  | Extern of extern_def node
```

---

## typing/typing.ml

Type checking and well-formedness validation.

### Main Entry Point

```ocaml
(* Type check a complete program *)
val tc_program : Ast.program list -> (penv * Ctbl.t) Result.t
```

### Type Environments

```ocaml
type tenv = {
  ctxt: ity M.t;              (* Variable type bindings *)
  ctbl: Ctbl.t;               (* Class information *)
  grps: (ident * ident list) list;  (* Datagroups *)
  exts: ident list;             (* Extern types *)
}

val initial_tenv : tenv

type bi_tenv = {
  left_tenv: tenv;
  right_tenv: tenv;
  bipreds: bipred_params M.t;
}

val initial_bi_tenv : bi_tenv
```

### Expression Type Checking

```ocaml
(* Type check an expression *)
val tc_exp : tenv -> Ast.exp -> Annot.ity Result.t

(* Type check a list of expressions *)
val tc_exp_list : tenv -> Ast.exp list -> Annot.ity list Result.t
```

### Formula Type Checking

```ocaml
(* Type check a formula *)
val tc_formula : tenv -> Ast.formula -> unit Result.t

(* Type check a specification *)
val tc_spec : tenv -> Ast.spec -> unit Result.t
```

### Program Environment

```ocaml
type penv = Annot.definition M.t

(* Find definitions in environment *)
val find_interface : penv -> ident -> Annot.interface_def
val find_module : penv -> ident -> Annot.module_def
val find_bimodule : penv -> ident -> Annot.bimodule_def
```

### Utility Functions

```ocaml
(* Type predicates *)
val is_array_ty : Annot.ity -> bool
val is_class_ty : Annot.ity -> bool
val is_math_ty : Annot.ity -> bool

(* Operator types *)
val binop_ty : Ast.binop -> Annot.ity * Annot.ity * Annot.ity
val unrop_ty : Ast.unrop -> Annot.ity * Annot.ity

(* Type string representation *)
val string_of_ity : Annot.ity -> string
```

---

## typing/annot.ml

Type-annotated syntax trees.

### Intermediate Type System

```ocaml
type ity =
  | Tint
  | Tbool
  | Trgn
  | Tprop
  | Tclass of id * params
  | Tanyclass
  | Tmath of id * ity option

(* Type-annotated expressions *)
type exp = {
  exp_desc: exp_desc;
  exp_type: ity;
}

and exp_desc =
  | Econst of const_exp
  | Evar of id
  | Ebinop of binop * exp * exp
  | (* ... *)

(* Type-annotated formulas *)
type formula = {
  formula_desc: formula_desc;
  formula_name: id option;
}

and formula_desc =
  | Ftrue | Ffalse
  | Fexp of exp
  | (* ... *)

(* Type-annotated programs *)
type definition =
  | Unary_interface of interface_def
  | Module of module_def
  | Biinterface of biinterface_def
  | Bimodule of bimodule_def
  | Datagroup of datagroup_def
  | Extern of extern_def

type program = definition list
```

### Utility Functions

```ocaml
(* Get human-readable name for type *)
val string_of_ity : ity -> string

(* Get human-readable name for identifier *)
val id_name : id -> string

(* Extract from annotated structure *)
val exp_type : exp -> ity
val formula_type : formula -> ity option
```

---

## typing/ctbl.ml

Class table - storage for class definitions and metadata.

### Main API

```ocaml
type t

(* Create empty class table *)
val empty : t

(* Look up definitions *)
val find_class : t -> ident -> class_info
val find_interface : t -> ident -> interface_info
val find_module : t -> ident -> module_info
val find_method : t -> ident -> ident -> method_info

(* Add definitions *)
val add_class : t -> ident -> class_info -> t
val add_interface : t -> ident -> interface_info -> t
val add_module : t -> ident -> module_info -> t

(* Access internals *)
val classes : t -> class_info M.t
val interfaces : t -> interface_info M.t
val modules : t -> module_info M.t
val methods : t -> method_info M.t

(* Queries *)
val is_class : t -> ident -> bool
val is_interface : t -> ident -> bool
val is_module : t -> ident -> bool

(* Encapsulation *)
val is_public : t -> ident -> ident -> bool
val is_private : t -> ident -> ident -> bool

(* Debug *)
val debug_print_ctbl : out_channel -> t -> unit
```

### Information Records

```ocaml
type class_info = {
  c_name: ident;
  c_fields: (ident * ity) list;
  c_super: ident option;
  c_rep: ident option;
}

type interface_info = {
  i_name: ident;
  i_methods: (ident * method_sig) list;
}

type module_info = {
  m_name: ident;
  m_interface: ident;
  m_classes: class_info M.t;
}

type method_sig = {
  ms_params: (ident * ity) list;
  ms_return: ity option;
}
```

---

## pretrans/pretrans.ml

Pre-translation analysis and transformations.

### Main Entry Point

```ocaml
(* Process program environment with all analyses *)
val process : Ctbl.t -> penv -> penv
```

### Sub-modules

```ocaml
(* Expand specifications with invariants *)
module Expand_method_spec : sig
  val expand : penv -> penv
end

(* Validate encapsulation *)
module Encap_check : sig
  val check : Ctbl.t -> penv -> unit Result.t
end

(* Derive bimodule interfaces *)
module Derive_biinterface : sig
  val derive : penv -> penv
end

(* Resolve datagroup wildcards *)
module Resolve_datagroups : sig
  val resolve : penv -> penv
end

(* Generate frame lemmas *)
module Generate_frame_lemmas : sig
  val generate : penv -> penv
end
```

### Configuration

```ocaml
(* Control simplification *)
val simplify_effects : bool ref

(* Control which passes run *)
(* Set via command-line flags *)
```

---

## translate/translate.ml

Translation to Why3 parse trees.

### Main Entry Point

```ocaml
(* Compile program environment to Why3 *)
val compile_penv : ctxt -> penv -> Why3.Ptree.mlw_file list

(* Build initial translation context *)
module Build_State : sig
  val mk : (penv * Ctbl.t) -> (ctxt * Why3.Ptree.mlw_file)
end
```

### Translation Functions

```ocaml
(* Translate individual constructs *)
val trans_exp : ctxt -> Annot.exp -> Why3.Ptree.expr
val trans_formula : ctxt -> Annot.formula -> Why3.Ptree.term
val trans_command : ctxt -> Annot.command -> Why3.Ptree.expr
val trans_method : ctxt -> method_def -> Why3.Ptree.decl

(* Translate specifications *)
val trans_precond : ctxt -> Annot.spec -> Why3.Ptree.term
val trans_postcond : ctxt -> Annot.spec -> Why3.Ptree.term
```

### Translation Context

```ocaml
type ctxt = {
  ctbl: Ctbl.t;
  ident_map: (ident_kind * Why3.Ptree.qualid) M.t;
  field_map: Why3.Ptree.ident M.t;
  inst_map: S.t M.t;
  (* ... more fields ... *)
}

type ident_kind =
  | Id_local of ity
  | Id_global of ity
  | Id_logic
  | Id_other
  | Id_extern
```

### Convention Constants

```ocaml
(* Naming conventions *)
val mk_reftype_ctor : ident -> Why3.Ptree.ident
val mk_field_str : ident -> ident -> string
val mk_field_ident : ident -> ident -> Why3.Ptree.ident
val mk_ctor_name : ident -> Why3.Ptree.ident
val mk_alloc_name : ident -> Why3.Ptree.ident

(* Examples *)
(* Cell → "Cell" *)
(* M::MyClass → "M_MyClass" *)
(* Cell.value → "cell_value" *)
```

---

## util/lib.ml

General utility functions.

### List Utilities

```ocaml
(* Map with flattening *)
val concat_map : ('a -> 'b list) -> 'a list -> 'b list

(* Right fold *)
val foldr : ('a -> 'b -> 'b) -> 'b -> 'a list -> 'b

(* Right map *)
val mapr : ('a -> 'b) -> 'a list -> 'b list

(* Get last element *)
val last : 'a list -> 'a

(* Create range *)
val range : int -> int -> int list

(* Zip two lists *)
val zip : 'a list -> 'b list -> ('a * 'b) list
```

### Option Utilities

```ocaml
(* Lift option *)
val opt_map : ('a -> 'b) -> 'a option -> 'b option

(* Option to list *)
val opt_to_list : 'a option -> 'a list

(* Filter options *)
val filter_some : 'a option list -> 'a list
```

### Result Monad

```ocaml
type 'a t = Ok of 'a | Error of string

(* Monadic operators *)
val ( let* ) : 'a t -> ('a -> 'b t) -> 'b t
val ( let+ ) : 'a t -> ('a -> 'b) -> 'b t

(* Conversion *)
val to_option : 'a t -> 'a option
val of_option : 'a option -> string -> 'a t

(* Execution *)
val iter : ('a -> unit) -> 'a t -> unit
val map : ('a -> 'b) -> 'a t -> 'b t
```

### String Utilities

```ocaml
(* String predicates *)
val starts_with : string -> string -> bool
val ends_with : string -> string -> bool

(* Case conversion *)
val capitalize : string -> string
val lowercase : string -> string

(* Joining *)
val join : string -> string list -> string
```

### Map Utilities

```ocaml
(* Standard map operations *)
module M : sig
  type 'a t = 'a M.t
  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
  val find_opt : key -> 'a t -> 'a option
  val remove : key -> 'a t -> 'a t
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val map : ('a -> 'b) -> 'a t -> 'b t
  val bindings : 'a t -> (key * 'a) list
  (* ... *)
end
```

---

## util/why3util.ml

Why3 parse tree construction helpers.

### Identifier Construction

```ocaml
(* Create Why3 identifier *)
val mk_ident : string -> Why3.Ptree.ident

(* Create qualified identifier *)
val mk_qualid : string list -> Why3.Ptree.qualid
```

### Type Construction

```ocaml
(* Build type expressions *)
val mk_tvar : string -> Why3.Ptree.expr
val mk_tclass : string -> Why3.Ptree.expr
val mk_tarrow : Why3.Ptree.expr -> Why3.Ptree.expr -> Why3.Ptree.expr
```

### Term/Expression Construction

```ocaml
(* Constants *)
val mk_const : Why3.Number.number -> Why3.Ptree.expr
val mk_int : int -> Why3.Ptree.expr
val mk_bool : bool -> Why3.Ptree.expr

(* Variables *)
val mk_var : string -> Why3.Ptree.expr

(* Operations *)
val mk_binop : Ast.binop -> Why3.Ptree.expr -> Why3.Ptree.expr -> Why3.Ptree.expr
val mk_unop : Ast.unrop -> Why3.Ptree.expr -> Why3.Ptree.expr

(* Application *)
val mk_app : Why3.Ptree.expr -> Why3.Ptree.expr list -> Why3.Ptree.expr
```

### Formula Construction

```ocaml
(* Logical connectives *)
val mk_and : Why3.Ptree.term -> Why3.Ptree.term -> Why3.Ptree.term
val mk_or : Why3.Ptree.term -> Why3.Ptree.term -> Why3.Ptree.term
val mk_not : Why3.Ptree.term -> Why3.Ptree.term
val mk_impl : Why3.Ptree.term -> Why3.Ptree.term -> Why3.Ptree.term

(* Quantifiers *)
val mk_forall : (string * Why3.Ptree.expr) list -> Why3.Ptree.term -> Why3.Ptree.term
val mk_exists : (string * Why3.Ptree.expr) list -> Why3.Ptree.term -> Why3.Ptree.term
```

### Declaration Construction

```ocaml
(* Function declarations *)
val mk_let : string -> Why3.Ptree.expr list -> Why3.Ptree.expr -> Why3.Ptree.decl

(* Axioms and lemmas *)
val mk_axiom : string -> Why3.Ptree.term -> Why3.Ptree.decl
val mk_lemma : string -> Why3.Ptree.term -> Why3.Ptree.decl
```

---

## parser/parser.mly

Grammar specification (Menhir format).

### Entry Points

```menhir
%start top          (* Main entry point for files *)

top:
  | program_list EOF { $1 }

program_list:
  | { [] }
  | program program_list { $1 :: $2 }
```

### Key Grammar Rules

```menhir
(* Type expressions *)
ty:
  | IDENT { Tctor(Id $1, []) }
  | IDENT LT ty_list GT { Tctor(Id $1, $3) }

(* Expressions *)
exp:
  | CONST { no_loc (Econst $1) }
  | IDENT { no_loc (Evar (Id $1)) }
  | exp PLUS exp { no_loc (Ebinop(Plus, $1, $3)) }

(* Formulas *)
formula:
  | TRUE { Ftrue }
  | exp { Fexp $1 }
  | formula AND formula { Fconn(Conj, $1, $3) }

(* Commands *)
command:
  | SKIP { no_loc Skip }
  | IDENT ASSIGN exp { no_loc (Assign(Id $1, $3)) }
  | IDENT COLONEQUAL NEW IDENT { no_loc (New_class(Id $1, Id $4)) }
```

---

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
(* Entry point *)
val run : unit -> unit

(* Parsing phase *)
val parse_file : string -> Ast.program list
val parse_program : string list -> Ast.program list

(* Type checking phase *)
val typecheck_program : Ast.program list -> (penv * Ctbl.t)

(* Output handling *)
val set_output : string -> unit
val close_output : unit -> unit
val get_formatter : unit -> Format.formatter
```

---

## Data Type Reference

### Map Type

```ocaml
(* Generic map for storing definitions *)
module M : sig
  type key = Ast.ident
  type 'a t = (key * 'a) list  (* Simplified representation *)
  
  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
  val find_opt : key -> 'a t -> 'a option
  val iter : (key -> 'a -> unit) -> 'a t -> unit
  val map : ('a -> 'b) -> 'a t -> 'b t
end
```

### Set Type

```ocaml
(* Generic set for storing unique identifiers *)
module S : sig
  type elt = string
  type t
  
  val empty : t
  val add : elt -> t -> t
  val remove : elt -> t -> t
  val mem : elt -> t -> bool
  val iter : (elt -> unit) -> t -> unit
end
```

---

## Common Patterns

### Result Monad Pattern

```ocaml
(* Chain operations with error handling *)
let my_process () : 'a Result.t =
  let* file_contents = parse_file "input.rl" in
  let* (penv, ctbl) = tc_program file_contents in
  let* () = validate_encapsulation ctbl penv in
  Ok penv
```

### Class Table Lookup Pattern

```ocaml
(* Safe lookup with pattern matching *)
match Ctbl.find_class ctbl class_name with
| exception Not_found -> 
  Error (Printf.sprintf "Class not found: %s" (string_of_ident class_name))
| class_info ->
  (* Process class_info *)
```

### Environment Threading Pattern

```ocaml
(* Pass environment through computations *)
let rec tc_command_seq tenv commands =
  match commands with
  | [] -> Ok ()
  | cmd :: rest ->
    let* _ = tc_command_single tenv cmd in
    let updated_tenv = update_context tenv cmd in
    tc_command_seq updated_tenv rest
```

---

## See Also

- **CODEBASE_DOCUMENTATION.md** - Comprehensive descriptions
- **QUICK_REFERENCE.md** - Quick lookup tables
- **ARCHITECTURE.md** - Design patterns and data flow
- Source code comments in individual modules

