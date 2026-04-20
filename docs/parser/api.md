# Parser API Reference

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
Econst(Eint 42)              (* Integer literal *)
Evar(Id "x")                 (* Variable *)
Ebinop(Plus, E1, E2)         (* Arithmetic *)
Ecall(Id "foo", [E1; E2])    (* Method call *)
Esingleton(Evar x)           (* Singleton set {x} *)
Eimage(Evar obj, Id "field") (* Object.field *)
```


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
Ftrue / Ffalse               (* Boolean constants *)
Fexp(E)                      (* Expression as formula *)
Fpointsto(x, f, v)           (* x.f ↦ v *)
Fsubseteq(A, B)              (* A ⊆ B *)
Fquant(Forall, [qb], F)      (* ∀ qb . F *)
Fconn(Conj, F1, F2)          (* F1 ∧ F2 *)
```


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
Skip                         (* skip *)
Assign(x, E)                 (* x := E *)
New_class(x, "Cell")         (* x := new Cell *)
Field_assign(x, f, E)        (* x.f := E *)
Havoc(x)                     (* havoc x (nondeterministic) *)
```


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
