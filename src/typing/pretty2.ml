(* Pretty printer functions for the following data types

type ident = Ast.ident

(* Ast ident is 

type ident =
  | Id of string
  | Qualid of string * string list

Ast binop is

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

Ast unrop is

type unrop =
  | Uminus
  | Not

Ast connective is

type connective =
  | Conj | Disj | Imp | Iff

Ast quantifier is

type quantifier =
  | Forall | Exists

Ast effect kind is

type effect_kind = Read | Write

Ast modifier is

type modifier =
  | Ghost                       (* always public *)
  | Public
  | Modscope

Ast fannot is

type fannot =
  | Public_invariant
  | Private_invariant

Ast import_kind is

type import_kind =
  | Iregular
  | Itheory

*)

(* Extract a string from a non-qualified identifier. *)
let id_name id : string =
  match id with
  | Ast.Id name -> name
  | Ast.Qualid _ -> failwith ("id_name: " ^ Astutil.string_of_ident id)

let ident str : ident = Ast.Id str

type ity =
  | Tint
  | Tbool
  | Trgn
  | Tunit
  | Tprop
  | Tdatagroup
  | Tanyclass
  | Tclass of ident
  | Tmath of ident * ity option
  | Tmeth of { params: ity list; ret: ity }
  | Tfunc of { params: ity list; ret: ity }

let rec equiv_ity t t' =
  let open List in
  match t, t' with
  | Tclass _, Tanyclass
  | Tanyclass, Tclass _ -> true
  | Tmath (m, t), Tmath (m',t') -> m = m' && equiv_ity_opt t t'
  | Tmeth m, Tmeth m' ->
    length m.params = length m'.params
    && for_all2 equiv_ity m.params m'.params
    && equiv_ity m.ret m.ret
  | Tfunc f, Tfunc f' ->
    length f.params = length f'.params
    && for_all2 equiv_ity f.params f'.params
    && equiv_ity f.ret f'.ret
  | _ -> t = t'

and equiv_ity_opt t t' =
  match t, t' with
  | Some t, Some t' -> equiv_ity t t'
  | _, _ -> t = t'

let rec equiv_ity_pairs tys =
  List.fold_right (fun (s,t) b -> equiv_ity s t && b) tys true

let rec string_of_ity ity =
  match ity with
  | Tint -> "int"
  | Trgn -> "rgn"
  | Tbool -> "bool"
  | Tunit -> "unit"
  | Tprop -> "<prop>"
  | Tmath (name, Some ty) ->
    "%(" ^ string_of_ity ty ^ " " ^ Astutil.string_of_ident name ^ ")"
  | Tmath (name, None) -> "%(" ^ Astutil.string_of_ident name ^ ")"
  | Tclass name -> Astutil.string_of_ident name
  | Tanyclass -> "<class>"
  | Tdatagroup -> "<datagroup>"
  | Tmeth _ -> "<method>"
  | Tfunc _ -> "<function>"

let rec qualify_ity ity qual =
  let open Astutil in
  match ity with
  | Tint | Trgn | Tbool | Tunit | Tprop | Tanyclass | Tdatagroup -> ity
  | Tclass name -> Tclass (qualify_ident name (Some qual))
  | Tmath (name, Some ty) ->
    Tmath (qualify_ident name (Some qual), Some (qualify_ity ty qual))
  | Tmath (name, None) -> Tmath (qualify_ident name (Some qual), None)
  | Tmeth m ->
    Tmeth { params = map (flip qualify_ity qual) m.params;
            ret = qualify_ity m.ret qual }
  | Tfunc f ->
    Tfunc { params = map (flip qualify_ity qual) f.params;
            ret = qualify_ity f.ret qual }

(* 'a t is the type of an annotated 'a *)
type 'a t = { ty: ity; node: 'a }

let annot ty node = { node; ty }

let ( -: ) node ty = { node; ty }

type classname = ident

type binop = Ast.binop and unrop = Ast.unrop

type exp =
  | Econst of const_exp t
  | Evar of ident t
  | Ebinop of Ast.binop * exp t * exp t
  | Eunrop of Ast.unrop * exp t
  | Esingleton of exp t
  | Eimage of exp t * ident t
  | Esubrgn of exp t * classname
  | Ecall of ident t * exp t list
  | Einit of exp t

and const_exp =
  | Enull | Eunit | Eint of int | Ebool of bool | Eemptyset

type let_bound_value =
  | Lloc of ident t * ident t
  | Larr of ident t * exp t
  | Lexp of exp t

type let_bind = {
  value: let_bound_value t;
  is_old: bool;
  is_init: bool;
}

type connective = Ast.connective and quantifier = Ast.quantifier

(* NOTE: formulas by themselves need not be annotated with a type.
   This is because the only annotation one may use is Prop (this
   type of annotation is not expressible in our source language).

   However, identifiers and expressions inside formulas need to be
   annotated.
*)
type formula =
  | Ftrue
  | Ffalse
  | Fexp of exp t
  | Finit of let_bound_value t
  | Fnot of formula
  | Fpointsto of ident t * ident t * exp t
  | Farray_pointsto of ident t * exp t * exp t
  | Fsubseteq of exp t * exp t
  | Fdisjoint of exp t * exp t
  | Fmember of exp t * exp t
  | Flet of ident t * let_bind t * formula
  | Fconn of connective * formula * formula
  | Fquant of quantifier * qbinders * formula
  | Fold of exp t * let_bound_value t
  | Ftype of exp t * classname list

and qbinders = qbind list

and qbind = {name: ident t; in_rgn: exp t option; is_non_null: bool}

type effect_kind = Ast.effect_kind

type effect_desc =
  | Effvar of ident t
  | Effimg of exp t * ident t

type effect_elt = {
  effect_kind: effect_kind;
  effect_desc: effect_desc t;
}

type effect = effect_elt list

type boundary_decl = effect_desc t list

type atomic_command =
  | Skip                                          (* skip *)
  | Assign of ident t * exp t                     (* x := E *)
  | Havoc of ident t                              (* havoc x *)
  | New_class of ident t * classname              (* x := new K *)
  | New_array of ident t * classname * exp t      (* x := new T[E] *)
  | Field_deref of ident t * ident t * ident t    (* y := x.f *)
  | Field_update of ident t * ident t * exp t     (* x.f := E *)
  | Array_access of ident t * ident t * exp t     (* x := a[E] *)
  | Array_update of ident t * exp t * exp t       (* a[E] := E *)
  | Call of ident t option * ident t * ident t list (* x := m( E* ) *)

type modifier = Ast.modifier

type command =
  | Acommand of atomic_command
  | Vardecl of ident t * modifier option * ity * command
  | Seq of command * command
  | If of exp t * command * command
  | While of exp t * while_spec * command
  | Assume of formula
  | Assert of formula

and while_spec = {
  winvariants: formula list;
  wvariant: exp t option;
  wframe: effect;
}

type spec_elt =
  | Precond of formula
  | Postcond of formula
  | Effects of effect

type spec = spec_elt list

type field_decl = {
  field_name: ident t;
  field_ty: ity;
  attribute: modifier;
}

type class_decl = {
  class_name: classname;
  fields: field_decl list;
}

type class_def = Class of class_decl

type meth_decl = {
  meth_name: ident t;
  params: meth_param_info list;
  result_ty: ity;
  result_is_non_null: bool;
  meth_spec: spec;
  can_diverge: bool;
}

and meth_param_info = {
  param_name: ident t;
  param_modifier: modifier option;
  param_ty: ity;
  is_non_null: bool;
}

type meth_def = Method of meth_decl * command option

type named_formula = {
  kind: [`Axiom | `Lemma | `Predicate];
  annotation: Ast.fannot option;
  formula_name: ident t;
  params: ident t list;
  body: formula;
}

type inductive_predicate = {
  ind_name: ident t;
  ind_params: ident t list;
  ind_cases: (ident * formula) list;
}

type import_kind = Ast.import_kind

type import_directive = {
  import_kind: import_kind;
  import_name: ident;
  import_as: ident option;
  related_by: ident option;
}

type extern_decl =
  | Extern_type of ident * ident
  | Extern_const of ident * ity
  | Extern_axiom of ident
  | Extern_lemma of ident
  | Extern_predicate of { name: ident; params: ity list }
  | Extern_function of { name: ident; params: ity list; ret: ity }
  | Extern_bipredicate of { name: ident; lparams: ity list; rparams: ity list }

type interface_elt =
  | Intr_cdecl of class_decl
  | Intr_mdecl of meth_decl
  | Intr_vdecl of modifier * ident t * ity
  | Intr_boundary of boundary_decl
  | Intr_datagroup of ident list
  | Intr_formula of named_formula
  | Intr_import of import_directive
  | Intr_extern of extern_decl
  | Intr_inductive of inductive_predicate

type interface_def = {
  intr_name: ident;
  intr_elts: interface_elt list;
}

type module_elt =
  | Mdl_cdef of class_def
  | Mdl_mdef of meth_def
  | Mdl_vdecl of modifier * ident t * ity
  | Mdl_datagroup of ident * ident t list
  | Mdl_formula of named_formula
  | Mdl_import of import_directive
  | Mdl_extern of extern_decl
  | Mdl_inductive of inductive_predicate

type module_def = {
  mdl_name: ident;
  mdl_interface: ident;
  mdl_elts: module_elt list;
}

type value_in_state =
  | Left of exp t
  | Right of exp t

type biexp =
  | Bibinop of binop * biexp t * biexp t
  | Biconst of const_exp t
  | Bivalue of value_in_state t

type rformula =
  | Rprimitive of {name: ident; left_args: exp t list; right_args: exp t list}
  | Rbiequal of exp t * exp t
  | Rbiexp of biexp t
  | Ragree of exp t * ident t
  | Rboth of formula
  | Rleft of formula
  | Rright of formula
  | Rnot of rformula
  | Rconn of connective * rformula * rformula
  | Rquant of quantifier * rqbinders * rformula
  | Rlet of rlet_binder option * rlet_binder option * rformula
  | Rlater of rformula

and rlet_binder = ident t * ity * let_bind t

and rqbinders = qbinders * qbinders

type bicommand =
  | Bihavoc_right of ident t * rformula
  | Bisplit of command * command
  | Bisync of atomic_command
  | Bivardecl of varbind option * varbind option * bicommand
  | Biseq of bicommand * bicommand
  | Biif of exp t * exp t * bicommand * bicommand
  | Biif4 of exp t * exp t * fourwayif
  | Biwhile of exp t * exp t * alignment_guard * biwhile_spec * bicommand
  | Biassume of rformula
  | Biassert of rformula
  | Biupdate of ident t * ident t (* Update the refperm *)

and fourwayif = {
  then_then: bicommand;
  then_else: bicommand;
  else_then: bicommand;
  else_else: bicommand
}

and alignment_guard = rformula * rformula

and varbind = ident t * modifier option * ity

and biwhile_spec = {
  biwinvariants: rformula list;
  biwframe: effect * effect;
  biwvariant: biexp t option;
}

type named_rformula = {
  kind: [`Axiom | `Lemma | `Predicate];
  biformula_name: ident;
  biparams: (ident t * ity) list * (ident t * ity) list;
  body: rformula;
  is_coupling: bool;
}

type bispec_elt =
  | Biprecond of rformula
  | Bipostcond of rformula
  | Bieffects of effect * effect

type bispec = bispec_elt list

type bimeth_decl = {
  bimeth_name: ident;
  bimeth_left_params: meth_param_info list;
  bimeth_right_params: meth_param_info list;
  result_ty: ity * ity;
  result_is_non_null: bool * bool;
  bimeth_spec: bispec;
  bimeth_can_diverge: bool;
}

type bimeth_def = Bimethod of bimeth_decl * bicommand option

type bimodule_elt =
  | Bimdl_formula of named_rformula
  | Bimdl_mdef of bimeth_def
  | Bimdl_extern of extern_decl
  | Bimdl_import of import_directive

type bimodule_def = {
  bimdl_name: ident;
  bimdl_left_impl: ident;
  bimdl_right_impl: ident;
  bimdl_elts: bimodule_elt list;
}

type program_elt =
  | Unary_interface of interface_def
  | Unary_module of module_def
  | Relation_module of bimodule_def

type penv = program_elt M.t

taken from src/typing/annot.ml

M.t is 

module Ident : Map.OrderedType with type t = ident =
struct
  type t = ident
  let compare = compare
end

module M = Map.Make (Ident)

*)

open Annot
open Format

let pp_ident outf id = fprintf outf "%s" @@ Astutil.string_of_ident id

let pp_idents outf ids =
  pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@,") pp_ident outf ids

let pp_ity outf ty = fprintf outf "%s" @@ string_of_ity ty

let pp_binop outf (op: Ast.binop) =
  match op with
  | Plus   -> fprintf outf "+"
  | Minus  -> fprintf outf "-"
  | Mult   -> fprintf outf "*"
  | Div    -> fprintf outf "/"
  | Mod    -> fprintf outf "mod"
  | Equal  -> fprintf outf "="
  | Nequal -> fprintf outf "<>"
  | Leq    -> fprintf outf "<="
  | Geq    -> fprintf outf ">="
  | Gt     -> fprintf outf ">"
  | Lt     -> fprintf outf "<"
  | And    -> fprintf outf "and"
  | Or     -> fprintf outf "or"
  | Union  -> fprintf outf "union"
  | Inter  -> fprintf outf "inter"
  | Diff   -> fprintf outf "diff"

let max_precedence = 100        (* ` has max precedence *)

let binop_precedence (op: Ast.binop) =
  match op with
  | Union  -> 50
  | Inter  -> 50
  | Diff   -> 60
  | Mult   -> 40
  | Div    -> 40
  | Mod    -> 50
  | Plus   -> 30
  | Minus  -> 30
  | Equal  -> 20
  | Nequal -> 20
  | Leq    -> 10
  | Geq    -> 10
  | Gt     -> 10
  | Lt     -> 10
  | And    -> 5
  | Or     -> 3

let pp_unrop outf (op: Ast.unrop) =
  match op with
  | Uminus -> fprintf outf "-"
  | Not    -> fprintf outf "not"

let unrop_precedence (op: Ast.unrop) =
  match op with
  | Uminus -> 60
  | Not    -> 60

let rec pp_exp' k outf e =
  match e.node with
  | Econst ce -> fprintf outf "%a" pp_const_exp ce.node
  | Evar id -> fprintf outf "%a" pp_ident id.node
  | Ebinop (op, e1, e2) ->
    let prec = binop_precedence op in
    let pp' = pp_exp' prec in
    if k > prec
    then fprintf outf "@[(%a@ %a@ %a)@]" pp' e1 pp_binop op pp' e2
    else fprintf outf "@[%a@ %a@ %a@]" pp' e1 pp_binop op pp' e2
  | Eunrop (op, e) ->
    let prec = unrop_precedence op in
    let pp' = pp_exp' prec in
    if k > prec
    then fprintf outf "@[(%a@ %a)@]" pp_unrop op pp' e
    else fprintf outf "@[%a@ %a@]" pp_unrop op pp' e
  | Esingleton e -> fprintf outf "@[{%a}@]" (pp_exp' k) e
  | Eimage (g, f) ->
     fprintf outf "@[%a`%a@]" (pp_exp' max_precedence) g pp_ident f.node
  | Esubrgn (g, k) ->
     fprintf outf "@[%a of %a@]" pp_ident k (pp_exp' max_precedence) g
  | Ecall (fn, args) ->
     fprintf outf "@[%a(@[%a@])@]" pp_ident fn.node pp_exps args
  | Einit e ->
     fprintf outf "@[(init %a)@]" (pp_exp' k) e


and pp_exps outf exps =
  pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@,") pp_exp outf exps

and pp_const_exp outf ce =
  match ce with
  | Enull     -> fprintf outf "null"
  | Eunit     -> fprintf outf "()"
  | Eint i    -> fprintf outf "%d" i
  | Ebool b   -> fprintf outf "%B" b
  | Eemptyset -> fprintf outf "{}"

and pp_exp outf e = pp_exp' 0 outf e

let pp_let_bound_value outf e =
  match e with
  | Lloc (x, f) -> fprintf outf "@[%a.%a@]" pp_ident x.node pp_ident f.node
  | Larr (a, idx) -> fprintf outf "@[%a[%a]@]" pp_ident a.node pp_exp idx
  | Lexp e -> pp_exp outf e

let pp_let_bind outf e =
  let value = e.value.node in
  if e.is_old then fprintf outf "@[old(%a)@]" pp_let_bound_value value
  else pp_let_bound_value outf value

let pp_connective outf (conn: Ast.connective) =
  match conn with
  | Conj -> fprintf outf "/\\"
  | Disj -> fprintf outf "\\/"
  | Imp  -> fprintf outf "->"
  | Iff  -> fprintf outf "<->"

let connective_precedence (conn: Ast.connective) =
  match conn with
  | Conj -> 50
  | Disj -> 60
  | Imp  -> 30
  | Iff  -> 20

let pp_quantifier outf = function
  | Ast.Forall -> fprintf outf "@[forall@]"
  | Ast.Exists -> fprintf outf "@[exists@]"

let pp_ity_non_null is_non_null outf ty =
  if is_non_null then pp_ity outf ty else fprintf outf "@[%a?@]" pp_ity ty

let pp_qbinders outf qbinds =
  let pp_qbind out {name; in_rgn; is_non_null} =
    let x, t = name.node, name.ty in
    let pp_t = pp_ity_non_null is_non_null in
    match in_rgn with
    | None -> fprintf out "@[%a:%a@]" pp_ident x pp_t t
    | Some e -> fprintf outf "@[%a:%a@ in@ %a@]" pp_ident x pp_t t pp_exp e in
  pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@,") pp_qbind outf qbinds

  (* let pp_qbind out (x, eopt) =
   *   let (x, t) = x.node, x.ty in
   *   match eopt with
   *   | None -> fprintf out "@[%a:%a@]" pp_ident x pp_ity t
   *   | Some e -> fprintf out "@[%a:%a@ in@ %a@]" pp_ident x pp_ity t pp_exp e in
   * pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@,") pp_qbind outf qbinds *)

let rec pp_formula' k outf f =
  match f with
  | Ftrue -> pp_print_string outf "True"
  | Ffalse -> pp_print_string outf "False"
  | Fexp e -> pp_exp outf e
  | Fnot f ->
    if k < (unrop_precedence Ast.Not)
    then fprintf outf "@[~(%a)@]" (pp_formula' 60) f
    else fprintf outf "@[~%a@]" (pp_formula' 60) f
  | Fpointsto (x, f, e) ->
    fprintf outf "@[%a.%a@ =@ %a@]" pp_ident x.node pp_ident f.node pp_exp e
  | Farray_pointsto (a, idx, e) ->
    fprintf outf "@[%a[%a]@,=@ %a@]" pp_ident a.node pp_exp idx pp_exp e
  | Fdisjoint (e1, e2) ->
    fprintf outf "@[%a@ #@ %a@]" (pp_exp' 70) e1 (pp_exp' 70) e2
  | Fsubseteq (e1, e2) ->
    fprintf outf "@[%a@ subset@ %a@]" (pp_exp' 70) e1 (pp_exp' 70) e2
  | Fmember (e1, e2) ->
    fprintf outf "@[%a@ in@ %a@]" pp_exp e1 pp_exp e2
  | Ftype (e1, tys) ->
    fprintf outf "@[Type(%a,@ %a)@]" pp_exp e1 pp_idents tys
  | Finit e -> fprintf outf "@[init(%a)@]" pp_let_bound_value e.node
  | Fold (e, lbv) ->
    fprintf outf "@[old(%a)@,=@ %a@]" pp_exp e pp_let_bound_value lbv.node
  | Flet (x, v, f) ->
    fprintf outf "@[let@ %a@ =@ %a@ in@;%a@]"
      pp_ident x.node pp_let_bind v.node pp_formula f
  | Fconn (c, f1, f2) ->
    let prec = connective_precedence c in
    let pp' = pp_formula' prec in
    if k > prec
    then fprintf outf "@[(%a@ %a@ %a)@]" pp' f1 pp_connective c pp' f2
    else fprintf outf "@[%a@ %a@ %a@]" pp' f1 pp_connective c pp' f2
  | Fquant (q, qbinds, frm) ->
    fprintf outf "@[<b 2>(%a@ %a.@ @[%a@])@]"
      pp_quantifier q pp_qbinders qbinds pp_formula frm

and pp_formula outf f = pp_formula' 0 outf f

let pp_atomic_command outf ac =
  match ac with
  | Skip -> fprintf outf "@[%s@]" "skip"
  | Assign (x, e) -> fprintf outf "@[%a@ :=@ %a@]" pp_ident x.node pp_exp e
  | Havoc x -> fprintf outf "@[havoc %a@]" pp_ident x.node
  | New_class (x, name) ->
    fprintf outf "@[%a@ :=@ new@ %a@]" pp_ident x.node pp_ident name
  | New_array (a, ty, len) ->
    fprintf outf "@[%a@ :=@ new(%a)[%a]@]" pp_ident a.node pp_ident ty pp_exp len
  | Field_deref (y, x, f) ->
    let y = y.node and x = x.node and f = f.node in
    fprintf outf "@[%a@ :=@ %a.%a@]" pp_ident y pp_ident x pp_ident f
  | Field_update (x, f, e) ->
    fprintf outf "@[%a.%a@ :=@ %a@]" pp_ident x.node pp_ident f.node pp_exp e
  | Array_access (x, a, e) ->
    fprintf outf "@[%a@ :=@ %a[%a]@]" pp_ident x.node pp_ident a.node pp_exp e
  | Array_update (a, e1, e2) ->
    fprintf outf "@[%a[%a]@ :=@ %a@]" pp_ident a.node pp_exp e1 pp_exp e2
  | Call (x, meth, args) ->
    fprintf outf "@[%s%a(%a)@]"
      (match x with
       | Some id -> Astutil.string_of_ident id.node ^ " := "
       | None -> "")
      pp_ident meth.node
      pp_idents (List.map (fun e -> e.node) args)

let pp_atomic_command_special outf ac =
  match ac with
  | New_array (a, ty,  len) ->
    fprintf outf "@[%a@ :=@ new(%a){%a}@]"
      pp_ident a.node pp_ident ty pp_exp len
  | Array_access (x, a, e) ->
    fprintf outf "@[%a@ :=@ %a.{%a}@]"
      pp_ident x.node pp_ident a.node pp_exp e
  | Array_update (a, e1, e2) ->
    fprintf outf "@[%a.{%a}@ :=@ %a@]"
      pp_ident a.node pp_exp e1 pp_exp e2
  | _ -> pp_atomic_command outf ac

let pp_effect_kind outf = function
  | Ast.Read -> fprintf outf "rd"
  | Ast.Write -> fprintf outf "wr"

let pp_effect_desc outf = function
  | Effvar id -> pp_ident outf id.node
  | Effimg (g, f) -> let exp = Eimage (g, f) -: Trgn in pp_exp outf exp

let pp_effect_elt outf {effect_kind; effect_desc=desc} =
  (* fprintf outf "@[%a@ %a@]" pp_effect_kind effect_kind pp_effect_desc desc.node *)
  fprintf outf "@[<hv>%a@ %a@]" pp_effect_kind effect_kind pp_effect_desc desc.node

let pp_effect' outf eff =
  (* pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ";@;") pp_effect_elt outf eff *)
  let semi ppf () = Format.fprintf ppf " ;@ " in
  pp_print_list ~pp_sep:semi pp_effect_elt outf eff

let pp_effect outf eff = fprintf outf "@[%a@]" pp_effect' eff

let rec pp_value_in_state outf = function
  | Left e -> fprintf outf "@[[<%a<]@]" pp_exp e
  | Right e -> fprintf outf "@[[<%a<]@]"pp_exp e

let rec pp_biexp' k outf b =
  match b.node with
  | Biconst c -> fprintf outf "@[[%a]@]" pp_const_exp c.node
  | Bivalue v -> pp_value_in_state outf v.node
  | Bibinop (op, e1, e2) ->
    let prec = binop_precedence op in
    let pp' = pp_biexp' prec in
    if k > prec
    then fprintf outf "@[(%a@ %a@ %a)@]" pp' e1 pp_binop op pp' e2
    else fprintf outf "@[%a@ %a@ %a@]" pp' e1 pp_binop op pp' e2

let rec pp_rformula' k outf rfrm =
  let open List in
  match rfrm with
  | Rprimitive {name=fn; left_args=l; right_args=r} ->
    fprintf outf "@[%a@,(@[%a@]@ |@ @[%a@])@]" pp_ident fn pp_exps l pp_exps r
  | Rbiexp b -> pp_biexp' 0 outf b
  | Rnot rf ->
    if k > (unrop_precedence Ast.Not)
    then fprintf outf "@[~(%a)@]" (pp_rformula' 60) rf
    else fprintf outf "@[~%a@]" (pp_rformula' 60) rf
  | Rbiequal (e1, e2) ->
    begin match e1.node, e2.node with
      | Evar x, Evar y when x.node = y.node && e1.ty = e2.ty && x.ty = y.ty ->
        fprintf outf "@[Agree@ %a@]" pp_ident x.node
      | _ -> fprintf outf "@[%a@ =:=@ %a@]" pp_exp e1 pp_exp e2
    end
  | Ragree (g, f) ->
    fprintf outf "@[Agree@ %a`%a@]" (pp_exp' 70) g
      pp_ident f.node
  | Rboth f -> fprintf outf "@[Both@ (%a)@]" pp_formula f
  | Rleft f -> fprintf outf "@[<|@ %a@ <]@]" pp_formula f
  | Rright f -> fprintf outf "@[[>@ %a@ |>@]" pp_formula f
  | Rconn (c, rf1, rf2) ->
    let prec = connective_precedence c in
    let pp' = pp_rformula' prec in
    if k > prec
    then fprintf outf "@[(%a@ %a@ %a)@]" pp' rf1 pp_connective c pp' rf2
    else fprintf outf "@[%a@ %a@ %a@]" pp' rf1 pp_connective c pp' rf2
  | Rlet (Some (lid, lty, lval), Some (rid, rty, rval), rf) ->
    fprintf outf "@[let@ %a@ |@ %a@ =@ %a@ |@ %a@ in@;%a@]"
      pp_ident lid.node pp_ident rid.node
      pp_let_bind lval.node pp_let_bind rval.node
      pp_rformula rf
  | Rlet (Some (lid, lty, lval), None, rf) ->
    fprintf outf "@[let@ %a@ |@ =@ %a@ in@;%a@]"
      pp_ident lid.node
      pp_let_bind lval.node
      pp_rformula rf
  | Rlet (None, Some (rid, rty, rval), rf) ->
    fprintf outf "@[let@ |@ %a@ =@ %a@ in@;%a@]"
      pp_ident rid.node
      pp_let_bind rval.node
      pp_rformula rf
  | Rlet (None, None, _) -> assert false (* impossible *)
  | Rquant (q, (lbinds, rbinds), rfrm) ->
    fprintf outf "@[<b 2>(%a@ %a@ |@ %a.@ @[%a@])@]"
      pp_quantifier q pp_qbinders lbinds pp_qbinders rbinds pp_rformula rfrm
  | Rlater rf ->
    fprintf outf "@[ <>(%a)@]" pp_rformula rf

and pp_rformula outf f = pp_rformula' 0 outf f

let pp_bispec outf bispec =
  List.iter (function
      | Bieffects (e, e') ->
        fprintf outf "@[effects  @[{@[<h 2>@ %a@]@;|@[<h 2>@ %a@,@] }@]\n@]"
          pp_effect e pp_effect e'
      | Biprecond f ->
        fprintf outf "@[requires@ {@[<h 2>@ %a@ @]}@\n@]"
          pp_rformula f
      | Bipostcond f ->
        fprintf outf "@[ensures  {@[<h 2>@ %a@ @]}@\n@]"
          pp_rformula f
    ) bispec

let rec pp_command' outf c = match c with
  | Acommand ac -> pp_atomic_command outf ac
  | Vardecl (x, Some m, ty, c) ->
    fprintf outf "@[var@ %a@ %a@ :@ %a@ in@.@[%a@]@]"
      pp_modifier m pp_ident x.node pp_ity ty pp_command' c
  | Vardecl (x, None, ty, c) ->
    fprintf outf "@[var@ %a@ :@ %a@ in@.@[<hov 2>%a@]@]"
      pp_ident x.node pp_ity ty pp_command' c
  | Seq (c1, c2) -> fprintf outf "@[%a;@.%a@]" pp_command' c1 pp_command' c2
  | If (e, c1, c2) ->
    fprintf outf "@[if@ %a@;then@ %a@.else@ @[<hv 1>%a@]@ end@]"
      pp_exp e pp_command' c1 pp_command' c2
  | While (e, inv, c) ->
    fprintf outf
      "@[while@ %a@ do@.@[<b 2>%a@]@.@[<b 2>%a@]@.done@]"
      pp_exp e pp_while_spec inv pp_command' c
  | Assume f -> fprintf outf "@[assume@ {%a}@]" pp_formula f
  | Assert f -> fprintf outf "@[assert@ {%a}@]" pp_formula f

and pp_while_spec outf {winvariants; wframe} =
  let rec print_invariants invs = match invs with
    | [] -> ()
    | f :: fs ->
      fprintf outf "@[invariant @<v 2>[{%a}@] @]" pp_formula f;
      print_invariants fs
  in
  print_invariants winvariants; pp_effect outf wframe

and pp_modifier outf = function
  | Ast.Ghost -> fprintf outf "ghost"
  | Ast.Public -> ()
  | Ast.Modscope -> fprintf outf "modscope"

and pp_modifier_opt outf = function
  | Some modif -> pp_modifier outf modif
  | None -> ()

and pp_command outf c =
  let old_margin = get_margin () and old_indent = get_max_indent () in
  set_margin 10; set_max_indent 6;
  fprintf outf "@[<v 2>%a@]" pp_command' c;
  set_margin old_margin; set_max_indent old_indent

let pp_meth_param_info outf {param_name; param_modifier; param_ty; is_non_null} =
  fprintf outf "@[%a@ %a:@ %a@]"
    pp_modifier_opt param_modifier
    pp_ident param_name.node
    (pp_ity_non_null is_non_null) param_ty  

let pp_spec outf spec =
  List.iter (function
      | Precond f ->
        fprintf outf "@[requires@ {@[<h 2>@ %a@ @]}@\n@]" pp_formula f
      | Postcond f ->
        fprintf outf "@[ensures@ {@[<h 2>@ %a@ @]}@\n@]" pp_formula f
      | Effects eff ->
        fprintf outf "@[effects@ {@[<hFormat 2>@ %a@ @]}@\n@]" pp_effect eff
    ) spec


let pp_meth_decl outf {meth_name; params; result_ty; result_is_non_null;
                        meth_spec; can_diverge} =
  fprintf outf "@[<v 2>method@ %a(@[%a@])@ :@ %a@"
    pp_ident meth_name.node
    (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@ ") pp_meth_param_info) params
    (pp_ity_non_null (result_is_non_null)) result_ty;
  if can_diverge then fprintf outf " @<1>| diverges";
  fprintf outf "@.@[<v 2>%a@]@ end@]" pp_spec meth_spec 

let pp_field_decl outf {field_name; field_ty; attribute} =
  fprintf outf "@[%a@ %a:@ %a@]"
    pp_modifier attribute
    pp_ident field_name.node
    pp_ity field_ty

let pp_class_decl outf {class_name; fields} =
  fprintf outf "@[class@ %a@.@[<v 2>%a@.@]end@]"
    pp_ident class_name
    (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ";@ ") pp_field_decl) fields

let pp_class_def outf (Class c) = pp_class_decl outf c
let pp_meth_def outf (Method (m, body)) =
  fprintf outf "@[<v 2>%a@." pp_meth_decl m;
  match body with
  | Some c -> fprintf outf "@[<v 2>begin@ %a@ end@]@]" pp_command c
  | None -> fprintf outf "extern;@]"

let pp_named_formula outf {kind; annotation; formula_name; params; body} =
  let kind_str = match kind with
    | `Axiom -> "axiom"
    | `Lemma -> "lemma"
    | `Predicate -> "predicate"
  in
  fprintf outf "@[%s@ %a(@[%a@])@ =@.@[%a@]@ end@]"
    kind_str
    pp_ident formula_name.node
     pp_idents (List.map (fun e -> e.node) params)
    pp_formula body 

let pp_inductive_predicate outf {ind_name; ind_params; ind_cases} =
  fprintf outf "@[inductive@ %a(@[%a@])@ =@.@[<v 2>%a@]@ end@]"
    pp_ident ind_name.node
     pp_idents (List.map (fun e -> e.node) ind_params)
    (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf "@ |@ ")
       (fun outf (case_name, case_body) ->
          fprintf outf "@[%a:@ %a@]" pp_ident case_name pp_formula case_body))
    ind_cases

let pp_import_kind outf = function
  | Ast.Iregular -> fprintf outf "import"
  | Ast.Itheory -> fprintf outf "import_theory"

let pp_import_directive outf {import_kind; import_name; import_as; related_by} =
  fprintf outf "@[%a@ %a%s%s@;@]"
    pp_import_kind import_kind
    pp_ident import_name
    (match import_as with
     | Some id -> " as " ^ Astutil.string_of_ident id
     | None -> "")
    (match related_by with
     | Some id -> " related_by " ^ Astutil.string_of_ident id
     | None -> "")  

let pp_extern_decl outf = function
  | Extern_type (name, as_name) ->
    fprintf outf "@[extern type@ ";
    pp_ident outf name;
    fprintf outf "@ as@ ";
    pp_ident outf as_name;
  | Extern_const (name, ty) ->
    fprintf outf "@[extern const@ ";
    pp_ident outf name;
    fprintf outf "@ :@ %a;@]" pp_ity ty
  | Extern_axiom name ->
    fprintf outf "@[extern axiom@ ";
    pp_ident outf name;
    fprintf outf "@]" 
  | Extern_lemma name ->
    fprintf outf "@[extern lemma@ ";
    pp_ident outf name;
    fprintf outf "@]"
  | Extern_predicate {name; params} ->
    fprintf outf "@[extern predicate@ ";
    pp_ident outf name;
    fprintf outf "@[%a@];@]" (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@ ") pp_ity) params
  | Extern_function {name; params; ret} ->
    fprintf outf "@[extern function@ ";
    pp_ident outf name;
    fprintf outf "@[%a@]:@ %a;@]"
      (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@ ") pp_ity) params
      pp_ity ret
  | Extern_bipredicate {name; lparams; rparams} ->
    fprintf outf "@[extern bipredicate@ ";
    pp_ident outf name;
    fprintf outf "@[%a@]|@[%a@];@]" (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@ ") pp_ity) lparams
      (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@ ") pp_ity) rparams

(* Commented out due to type mismatches - needs updating to match current Annot types
let pp_interface_elt outf = function
  | Intr_cdecl c -> pp_class_decl outf c
  | Intr_mdecl m -> pp_meth_decl outf m
  | Intr_vdecl (modif, id, ty) ->   
    fprintf outf "@[var@ %a@ %a:@ %a;@]"
      pp_modifier modif
      pp_ident id.node
      pp_ity ty
  | Intr_boundary b -> pp_boundary_decl outf b
  | Intr_datagroup ids -> 
    fprintf outf "@[datagroup@ {@[%a@]}@;@]" pp_idents (List.map (fun e -> e.node) ids)
  | Intr_formula f -> pp_named_formula outf f
  | Intr_import imp -> pp_import_directive outf imp
  | Intr_extern ed -> pp_extern_decl outf ed
  | Intr_inductive ind -> pp_inductive_predicate outf ind *)

let pp_interface_def outf _ =
  fprintf outf "@[<v 2>interface@ (placeholder)@.@]"

(* Module printing stubbed out for now *)
let pp_module_elt outf _ = fprintf outf "(module_elt)"    

let pp_module_def outf _ = fprintf outf "(module_def)" 

let pp_value_in_state outf = function
  | Left e -> fprintf outf "@[[<%a<]@]" pp_exp e
  | Right e -> fprintf outf "@[[<%a<]@]"pp_exp e

let pp_varbind outf (id, modif, ty) =
  fprintf outf "@[%a@ %a:@ %a@]"
    pp_modifier_opt modif
    pp_ident id.node
    pp_ity ty

let pp_bicommand outf c =
  let old_margin = get_margin () and old_indent = get_max_indent () in
  set_margin 10; set_max_indent 6;
  let rec pp_bicommand' outf c = match c with
    | Bihavoc_right (x, f) -> 
      fprintf outf "@[Havocr@ %a@;on@ right@;@[%a@]@]" pp_ident x.node pp_rformula f
    | Bisplit (c1, c2) ->
      fprintf outf "@[Bisplit@;(@[%a@]@,@[%a@])@]" pp_command c1 pp_command c2
    | Bisync ac ->
      fprintf outf "@[Bisync@;@[%a@]@]" pp_atomic_command_special ac
    | Bivardecl (x, y, c) ->
      let pp_var_opt outf = function
        | Some v -> pp_varbind outf v
        | None -> fprintf outf "_"
      in
      fprintf outf "@[var@ %a@ |@ %a@ in@.%a@]"
        pp_var_opt x pp_var_opt y pp_bicommand' c
    | Biseq (c1, c2) -> fprintf outf "@[%a;@.%a@]" pp_bicommand' c1 pp_bicommand' c2 
    | Biif (e1, e2, c1, c2) ->
      fprintf outf "@[if@ %a@ |@ %a@;then@ %a@.else@ @[<hv 1>%a@]@ end@]"
        pp_exp e1 pp_exp e2 pp_bicommand' c1 pp_bicommand' c2
    | Biif4 (e1, e2, {then_then; then_else; else_then; else_else}) ->
      fprintf outf "@[if@ %a@ |@ %a@;then@ %a@.else@ %a@;@\n\
                    else@ %a@.else@ @[<hv 1>%a@]@ end@]"
        pp_exp e1 pp_exp e2 pp_bicommand' then_then pp_bicommand' then_else
        pp_bicommand' else_then pp_bicommand' else_else 
    | Biwhile (e1, e2, (ag1, ag2), spec, c) ->
      fprintf outf
        "@[while@ %a@ |@ %a@ do@.@[<b 2>%a@]@.done@]"
        pp_exp e1 pp_exp e2 pp_bicommand' c
    | Biassume f -> fprintf outf "@[assume@ {%a}@]" pp_rformula f
    | Biassert f -> fprintf outf "@[assert@ {%a}@]" pp_rformula f
    | Biupdate (x, y) ->
      fprintf outf "@[update_refperm@ %a@ |@ %a@]" pp_ident x.node pp_ident y.node
  in
  fprintf outf "@[<v 2>%a@]" pp_bicommand' c;
  set_margin old_margin; set_max_indent old_indent

let pp_bimeth_decl outf {bimeth_name; bimeth_left_params; bimeth_right_params;
                          result_ty; result_is_non_null; bimeth_spec; bimeth_can_diverge} =
  fprintf outf "@[<v 2>bimethod@ %a(@[%a@]|@[%a@])@ :@ %a@"
    pp_ident bimeth_name
    (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@ ") pp_meth_param_info) bimeth_left_params
    (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@ ") pp_meth_param_info) bimeth_right_params       
    (pp_ity_non_null (fst result_is_non_null)) (fst result_ty);
  if bimeth_can_diverge then fprintf outf " @<1>| diverges";
  fprintf outf "@.@[<v 2>%a@]@ end@]" pp_bispec bimeth_spec
let pp_bimeth_def outf (Bimethod (m, body)) =
  fprintf outf "@[<v 2>%a@." pp_bimeth_decl m;
  match body with
  | Some c -> fprintf outf "@[<v 2>begin@ %a@ end@]@]" pp_bicommand c
  | None -> fprintf outf "extern;@]"

let pp_named_rformula outf {kind; biformula_name; biparams; body; is_coupling} =
  let kind_str = match kind with
    | `Axiom -> "axiom"
    | `Lemma -> "lemma"
    | `Predicate -> "predicate"
  in
  let (lparams, rparams) = biparams in
  let pp_biparam outf (id, ty) = 
    fprintf outf "@[%a:@ %a@]" pp_ident id.node pp_ity ty
  in
  let pp_biparams outf (lparams, rparams) =
    fprintf outf "@[%a@]@ |@ @[%a@]"
      (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@ ") pp_biparam) lparams
      (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf ",@ ") pp_biparam) rparams
  in
  fprintf outf "@[%s@ %a(@[%a@])@ =@.@[%a@]@ end@]"
    kind_str
    pp_ident biformula_name
    pp_biparams biparams
    pp_rformula body

let pp_bimodule_elt outf = function
  | Bimdl_formula f -> pp_named_rformula outf f
  | Bimdl_mdef m -> pp_bimeth_def outf m
  | Bimdl_extern ed -> pp_extern_decl outf ed
  | Bimdl_import imp -> pp_import_directive outf imp

let pp_bimodule_def outf {bimdl_name; bimdl_left_impl; bimdl_right_impl; bimdl_elts} =
  fprintf outf "@[<v 2>bimodule@ %a@ implements@ %a@ |@ %a@.@[<v 2>%a@]@.end@]"
    pp_ident bimdl_name
    pp_ident bimdl_left_impl
    pp_ident bimdl_right_impl
    (pp_print_list ~pp_sep:(fun outf _ -> fprintf outf "@.") pp_bimodule_elt) bimdl_elts

let pp_program outf _ =
  fprintf outf "@[<program_stub>@]"


  

let rec all_existify (b: bicommand) : bicommand =
  match b with
  | Bihavoc_right (x, rf) ->
    let xbind = {name = x; in_rgn = None; is_non_null = false} in
    let check = Rquant (Exists, ([], [xbind]), rf) in
    Printf.fprintf stderr "<< all_existify>>\n";
    let fmt = Format.formatter_of_out_channel stderr in
    pp_bicommand fmt b;
    Format.pp_print_flush fmt ();
    Printf.fprintf stderr "\n<<all_existify END>>\n";
    mk_biseq [Biassert check; Bihavoc_right (x, rf)]
  | Bisplit (c1, c2) -> Bisplit (c1, unary_all_existify c2)
  | Bisync ac -> Bisync ac
  | Bivardecl (l, r, body) -> Bivardecl (l, r, all_existify body)
  | Biseq (cc1, cc2) -> Biseq (all_existify cc1, all_existify cc2)
  | Biif (e, e', cc1, cc2) -> Biif (e, e', all_existify cc1, all_existify cc2)
  | Biif4 (e, e', bs) -> Biif4 (e, e', map_fourwayif all_existify bs)
  | Biupdate (x, y) -> Biupdate (x, y) (* "Link x with y" *)
  | Biassert rf -> Biassert rf
  | Biassume rf ->
    (* warn "Relational assumptions are not treated soundly except after right havocs."; *)
    Biassume rf
  | Biwhile (e, e', (lg, rg), annot, cc) when is_false_ag rg ->
    (* This loop never does right-only iterations so we don't need a variant *)
    Biwhile (e, e', (lg, rg), annot, all_existify cc)
  | Biwhile (e, e', (lg, rg), {biwframe; biwinvariants; biwvariant}, cc) ->
    begin match biwvariant with
      | None -> raise @@ Invalid_argument "all_existify: expected variant"
      | Some vnt ->
        let vfresh = mk_fresh_id "vnt" in
        let vnt_snap = Evar (vfresh -: vnt.ty) -: vnt.ty in
        let vnt_snap' = Bivalue (Right vnt_snap -: vnt.ty) -: vnt.ty in
        let zero = Biconst (Eint 0 -: Tint) -: Tint in
        let vnt_ge0 = Bibinop (Ast.Leq, zero, vnt_snap') in
        let vnt_dec = Bibinop (Ast.Lt, vnt, vnt_snap') in
        let vnt_ini = Rbiexp (Bibinop (Ast.Equal, vnt_snap', vnt) -: Tbool) in
        let hav_vnt = Bihavoc_right (vfresh -: vnt.ty, vnt_ini) in
        let bfresh = mk_fresh_id "b" in
        let b_snap = Evar (bfresh -: Tbool) -: Tbool in
        let b_snap' = Bivalue (Right b_snap -: Tbool) -: Tbool in
        let rgt_only : rformula =
          let lft_e = Rbiexp (Bivalue (Left e -: Tbool) -: Tbool) in
          let rgt_e' = Rbiexp (Bivalue (Right e' -: Tbool) -: Tbool) in
          let neg_lft = Rnot (Rconn (Ast.Conj, lft_e, lg)) in
          let enab_rgt = Rconn (Ast.Conj, rgt_e', rg) in
          Rconn (Ast.Conj, neg_lft, enab_rgt) in
        let b_ini = Rconn (Ast.Iff, Rbiexp b_snap', rgt_only) in
        let hav_b = Bihavoc_right (bfresh -: Tbool, b_ini) in
        let vnt_ge0_asrt =
          let vnt_ge0' = Rbiexp (vnt_ge0 -: Tbool) in
          Biassert (Rconn (Ast.Imp, Rbiexp b_snap', vnt_ge0')) in
        let vnt_dec_asrt =
          let vnt_dec' = Rbiexp (vnt_dec -: Tbool) in
          Biassert (Rconn (Ast.Imp, Rbiexp b_snap', vnt_dec')) in
        let body = mk_biseq [
            hav_vnt;
            hav_b;
            all_existify cc;
            vnt_ge0_asrt;
            vnt_dec_asrt;
          ] in
        let cc' =
          let v = vfresh -: vnt.ty, None, vnt.ty in
          let b = bfresh -: Tbool, None, Tbool in
          Bivardecl (None, Some v, Bivardecl (None, Some b, body)) in
        let biwvariant = None in
        Biwhile (e, e', (lg, rg), {biwframe; biwinvariants; biwvariant}, cc')
    end

and unary_all_existify (c: command) : command =
  match c with
  | Acommand (Call (x,m,args)) ->
    (* TODO: Add support for forward underapproximation specs *)
    (* c : P ~e~> Q  is the same as skip|c : [> P >] =e=> [> Q >] *)
    (* warn "Calls to procedures on the right are not treated soundly."; *)
    Acommand (Call (x,m,args))
  | Acommand ac -> Acommand ac
  | Assume f ->
    (* warn "Unary assumptions are not treated soundly."; *)
    Assume f
  | Assert f -> Assert f
  | Vardecl (c, m, ty, body) -> Vardecl (c, m, ty, unary_all_existify body)
  | Seq (c1, c2) -> Seq (unary_all_existify c1, unary_all_existify c2)
  | If (e, c1, c2) -> If (e, unary_all_existify c1, unary_all_existify c2)
  | While (e, spec, c) ->
    begin match spec.wvariant with
      | None -> raise @@ Invalid_argument "unary_all_existify: expected variant"
      | Some vnt ->
        let vfresh = mk_fresh_id "vnt" in
        let vnt_snap = Evar (vfresh -: vnt.ty) -: vnt.ty in 
        let vnt_snap_stmt = Acommand(Assign (vfresh -: vnt.ty, vnt)) in 
        let zero = Econst (Eint 0 -: Tint) -: Tint in
        let vnt_ge0 = Ebinop (Ast.Leq, zero, vnt_snap) in
        let vnt_dec = Ebinop (Ast.Lt, vnt, vnt_snap) in
        let vnt_ge0_asrt = Assert (Fexp (vnt_ge0 -: Tbool)) in
        let vnt_dec_asrt = Assert (Fexp (vnt_dec -: Tbool)) in
        let c' = unary_all_existify c in
        let c' = mk_seq [vnt_snap_stmt; c'; vnt_ge0_asrt; vnt_dec_asrt] in
        let spec = {spec with wvariant = None} in
        While (e, spec, Vardecl(vfresh -: vnt.ty, None, vnt.ty, c'))
    end
