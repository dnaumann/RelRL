# Translation API Reference

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
val trans_exp : ctxt -> Annot.exp -> Why3.Ptree.expr
val trans_formula : ctxt -> Annot.formula -> Why3.Ptree.term
val trans_command : ctxt -> Annot.command -> Why3.Ptree.expr
val trans_method : ctxt -> method_def -> Why3.Ptree.decl

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

### Naming Convention Helpers

```ocaml
val mk_reftype_ctor : ident -> Why3.Ptree.ident
val mk_field_str : ident -> ident -> string
val mk_field_ident : ident -> ident -> Why3.Ptree.ident
val mk_ctor_name : ident -> Why3.Ptree.ident
val mk_alloc_name : ident -> Why3.Ptree.ident

(* Examples:
   Cell       → "Cell"
   M::MyClass → "M_MyClass"
   Cell.value → "cell_value" *)
```
