# Typing API Reference

## typing/typing.ml

Type checking and well-formedness validation.

### Main Entry Point

```ocaml
(* Type check a complete program *)
val tc_program : Ast.program list -> (penv * Ctbl.t) Result.t
```


### Type Abbreviations
```ocaml
type ity = Annot.ity      (* Intermediate type *)
type ident = Ast.ident    (* Qualified/unqualified name *)
type loc = Ast.loc        (* Source location *)
type penv = definition M.t  (* Program environment *)
type ctbl = Ctbl.t        (* Class table *)
```


### Standard Maps
```ocaml
(* String → Type mapping *)
let env = M.empty
M.add (Id "x") Tint env

(* Class → Info mapping *)
Ctbl.classes ctbl  (* class_name → class_info *)
```


### Result Monad Pattern


```ocaml
let ( let* ) = Result.bind

let my_function () : 'a Result.t =
  let* x = parse_file "file.rl" in
  let* (penv, ctbl) = tc_program x in
  let* () = validate_encapsulation ctbl penv in
  Ok penv
```



### Type Environments

```ocaml
(* Annotated types *)
Tint, Tbool, Trgn, Tprop
Tclass(name)                 (* Class types *)
Tmath(name, Some ty)         (* Math types (for heap) *)

(* Type bindings *)
M.empty                      (* Empty context *)
M.add (Id "x") Tint env.ctxt (* Add binding *)
```

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
val tc_exp : tenv -> Ast.exp -> Annot.ity Result.t
val tc_exp_list : tenv -> Ast.exp list -> Annot.ity list Result.t
```

### Formula Type Checking

```ocaml
val tc_formula : tenv -> Ast.formula -> unit Result.t
val tc_spec : tenv -> Ast.spec -> unit Result.t
```

### Program Environment

```ocaml
type penv = Annot.definition M.t

val find_interface : penv -> ident -> Annot.interface_def
val find_module : penv -> ident -> Annot.module_def
val find_bimodule : penv -> ident -> Annot.bimodule_def
```

### Utility Functions

```ocaml
val is_array_ty : Annot.ity -> bool
val is_class_ty : Annot.ity -> bool
val is_math_ty : Annot.ity -> bool

val binop_ty : Ast.binop -> Annot.ity * Annot.ity * Annot.ity
val unrop_ty : Ast.unrop -> Annot.ity * Annot.ity

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

type exp = {
  exp_desc: exp_desc;
  exp_type: ity;
}

and exp_desc =
  | Econst of const_exp
  | Evar of id
  | Ebinop of binop * exp * exp
  | (* ... *)

type formula = {
  formula_desc: formula_desc;
  formula_name: id option;
}

and formula_desc =
  | Ftrue | Ffalse
  | Fexp of exp
  | (* ... *)

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
val string_of_ity : ity -> string
val id_name : id -> string
val exp_type : exp -> ity
val formula_type : formula -> ity option
```

---

## typing/ctbl.ml

Class table — storage for class definitions and metadata.

### Main API

```ocaml
type t

val empty : t

val find_class : t -> ident -> class_info
val find_interface : t -> ident -> interface_info
val find_module : t -> ident -> module_info
val find_method : t -> ident -> ident -> method_info

val add_class : t -> ident -> class_info -> t
val add_interface : t -> ident -> interface_info -> t
val add_module : t -> ident -> module_info -> t

val classes : t -> class_info M.t
val interfaces : t -> interface_info M.t
val modules : t -> module_info M.t
val methods : t -> method_info M.t

val is_class : t -> ident -> bool
val is_interface : t -> ident -> bool
val is_module : t -> ident -> bool

val is_public : t -> ident -> ident -> bool
val is_private : t -> ident -> ident -> bool

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
