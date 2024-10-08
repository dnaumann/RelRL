(** ast.ml -- abstract syntax of the object language. *)

type loc = {loc_fname: string; loc_line: int; loc_range: int * int}

let dummy_loc = {loc_fname = ""; loc_line = 0; loc_range = (0,0) }

type 'a node = { elt: 'a; loc: loc }

let no_loc elt = { elt; loc = dummy_loc }

type ident =
  | Id of string
  | Qualid of string * string list

(* FUTURE: Potentially model identifiers as follows: *)
module Ident : sig
  type t
  val name : t -> string
  val fresh : string -> t
  val refresh : t -> t
end = struct
  type t = Name of string
         | Gensym of string * int

  let count = ref 0

  let name = function
    | Name x -> x
    | Gensym(x,k) -> x ^ Int.to_string k

  let fresh = fun x -> incr count; Gensym(x, !count)

  let refresh = function
    | Name x | Gensym (x,_) -> incr count; Gensym (x, !count)
end

type ty =
  | Tctor of ident * ty node list

(* Primitive types *)
let int_ty  = Tctor(Id "int", [])
let bool_ty = Tctor(Id "bool", [])
let rgn_ty  = Tctor(Id "rgn", [])
let unit_ty = Tctor(Id "unit", [])

type modifier =
  | Ghost                       (* always public *)
  | Public
  | Modscope

type binop =
  | Plus
  | Minus
  | Mult
  | Div
  | Mod
  | Equal
  | Nequal
  | Leq
  | Lt
  | Geq
  | Gt
  | And
  | Or
  | Union
  | Inter
  | Diff

type unrop =
  | Uminus
  | Not

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

type let_bound_value =
  | Lloc of ident * ident
  | Larr of ident * exp node
  | Lexp of exp node

type let_bind = {
  value : let_bound_value node;
  is_old : bool;
  is_init : bool;
}

type formula =
  | Ftrue
  | Ffalse
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

and connective =
  | Conj | Disj | Imp | Iff

and quantifier =
  | Forall | Exists

and qbind = {
  name: ident;
  ty: ty node;
  in_rgn: exp node option;
  is_non_null: bool
}

and quantifier_bindings = qbind list

type effect_kind = Read | Write

type effect_desc =
  | Effvar of ident
  | Effimg of exp node * ident

type effect_elt = {
  effect_kind: effect_kind;
  effect_desc: effect_desc;
}

type effect = effect_elt node list

type boundary_decl = effect_desc node list

type atomic_command =
  | Skip                                         (* skip *)
  | Assign of ident * exp node                   (* x := E *)
  | Havoc of ident                               (* havoc x *)
  | New_class of ident * ident                   (* x := new K *)
  | New_array of ident * ident * exp node        (* x := new T[E] *)
  | Field_deref of ident * ident * ident         (* y := x.f *)
  | Field_update of ident * ident * exp node     (* x.f := E *)
  | Array_access of ident * ident * exp node     (* x := a[E] *)
  | Array_update of ident * exp node * exp node  (* a[E] := E *)
  | Call of ident option * ident * ident node list (* x := m( y* ) *)

type command =
  | Acommand of atomic_command node
  | Vardecl of ident * modifier option * ty node * command node
  | Seq of command node * command node
  | If of exp node * command node * command node
  | While of exp node * while_spec * command node
  | Assume of formula node
  | Assert of formula node

and while_spec = while_spec_elt node list

and while_spec_elt =
  | Winvariant of formula node
  | Wvariant of exp node
  | Wframe of effect node

type spec_elt =
  | Precond of formula node
  | Postcond of formula node
  | Effects of effect node

type spec = spec_elt node list

type field_decl = {
  field_name: ident;
  field_ty: ty node;
  attribute: modifier;
}

type class_decl = {
  class_name: ident;
  fields: field_decl node list;
}

type class_def = Class of class_decl node

type meth_decl = {
  meth_name: ident;
  params: meth_param_info list;
  result_ty: ty node;
  result_is_non_null: bool;
  meth_spec: spec node;
}

and meth_param_info = {
  param_name: ident;
  param_modifier: modifier option;
  param_ty: ty node;
  is_non_null: bool
}

type meth_def = Method of meth_decl node * command node option

type fannot =
  | Public_invariant
  | Private_invariant

type named_formula = {
  kind: [`Axiom | `Lemma | `Predicate];
  annotation: fannot option;
  formula_name: ident;
  params: (ident * ty node) list;
  body: formula node;
}

type inductive_predicate = {
  ind_name: ident;
  ind_params: (ident * ty node) list;
  ind_cases: (ident node * formula node) list;
}

type import_directive = {
  import_kind: import_kind;
  import_name: ident;
  import_as: ident option;
  related_by: ident option;
}

and import_kind =
  | Iregular
  | Itheory

type extern_decl = {
  extern_symbol: ident;
  extern_kind: extern_kind;
  extern_input: ty node list;
  extern_biinput: ty node list * ty node list;
  extern_output: ty node option;
  extern_default: ident option;
}

and extern_kind =
  | Ex_type
  | Ex_const
  | Ex_predicate
  | Ex_lemma
  | Ex_axiom
  | Ex_function
  | Ex_bipredicate

type interface_elt =
  | Intr_cdecl of class_decl node
  | Intr_mdecl of meth_decl node
  | Intr_vdecl of modifier * ident * ty node
  | Intr_boundary of boundary_decl node
  | Intr_datagroup of ident list
  | Intr_formula of named_formula node
  | Intr_import of import_directive node
  | Intr_extern of extern_decl node
  | Intr_inductive of inductive_predicate node

type interface_def = {
  intr_name: ident;
  intr_elts: interface_elt node list;
}

type module_elt =
  | Mdl_cdef of class_def node
  | Mdl_mdef of meth_def node
  | Mdl_vdecl of modifier * ident * ty node
  | Mdl_datagroup of ident * ident list
  | Mdl_formula of named_formula node
  | Mdl_import of import_directive node
  | Mdl_extern of extern_decl node
  | Mdl_inductive of inductive_predicate node

type module_def = {
  mdl_name: ident;
  mdl_interface: ident;
  mdl_elts: module_elt node list;
}

type value_in_state =
  | Left of exp node
  | Right of exp node

type biexp =
  | Bibinop of binop * biexp node * biexp node
  | Biconst of const_exp node
  | Bivalue of value_in_state node

type rformula =
  | Rprimitive of ident * value_in_state node list
  | Rbiequal of exp node * exp node
  | Rbiexp of biexp node
  | Ragree of exp node * ident
  | Rboth of formula node
  | Rleft of formula node
  | Rright of formula node
  | Rnot of rformula node
  | Rconn of connective * rformula node * rformula node
  | Rquant of quantifier * rquantifier_bindings * rformula node
  | Rlet of rlet_binding option * rlet_binding option * rformula node

and rlet_binding = ident * ty node option * let_bind node

and rquantifier_bindings = quantifier_bindings * quantifier_bindings

type bicommand =
  | Bihavoc_right of ident * rformula node
  | Bisplit of command node * command node
  | Bisync of atomic_command node
  | Bivardecl of varbind option * varbind option * bicommand node
  | Biseq of bicommand node * bicommand node
  | Biif of exp node * exp node * bicommand node * bicommand node
  | Biif4 of exp node * exp node
             * bicommand node * bicommand node
             * bicommand node * bicommand node
  | Biwhile of exp node * exp node * alignment_guard option
               * biwhile_spec * bicommand node
  | Biassume of rformula node
  | Biassert of rformula node
  | Biupdate of ident * ident    (* Update the refperm *)

and alignment_guard = rformula node * rformula node

and varbind = ident * modifier option * ty node

and biwhile_spec = biwhile_spec_elt node list

and biwhile_spec_elt =
  | Biwinvariant of rformula node
  | Biwframe of effect node * effect node
  | Biwvariant of biexp node

type named_rformula = {
  kind: [`Axiom | `Lemma | `Predicate];
  biformula_name: ident;
  biparams: (ident * ty node) list * (ident * ty node) list;
  body: rformula node;
  is_coupling: bool;
}

type bispec_elt =
  | Biprecond of rformula node
  | Bipostcond of rformula node
  | Bieffects of effect node * effect node

type bispec = bispec_elt node list

type bimeth_decl = {
  bimeth_name: ident;
  bimeth_left_params: meth_param_info list;
  bimeth_right_params: meth_param_info list;
  result_ty: ty node * ty node;
  result_is_non_null: bool * bool;
  bimeth_spec: bispec node;
}

type bimeth_def = Bimethod of bimeth_decl node * bicommand node option

type bimodule_elt =
  | Bimdl_formula of named_rformula node
  | Bimdl_mdef of bimeth_def node
  | Bimdl_extern of extern_decl node
  | Bimdl_import of import_directive node

type bimodule_def = {
  bimdl_name: ident;
  bimdl_left_impl: ident;     (* Left unary module *)
  bimdl_right_impl: ident;    (* Right unary module *)
  bimdl_elts: bimodule_elt node list;
}

type program_elt =
  | Unr_intr of interface_def node
  | Unr_mdl of module_def node
  | Rel_mdl of bimodule_def node

type program = program_elt node list
