(** annot.ml -- annotated syntax tree *)

open Lib

module M = Astutil.M

type ident = Ast.ident

(* Extract a string from a non-qualified identifier. *)
let id_name id : string =
  match id with
  | Ast.Id name -> name
  | Ast.Qualid _ -> failwith ("id_name: " ^ Astutil.string_of_ident id)

let ident str : ident = Ast.Id str

(* Defined to aid with type checking.

   For any K, Tanyclass is considered equivalent to Tclass K.  The
   type of null (by itself) is Tanyclass.  Predicates have type Tfunc
   {params; ret} where ret = Tprop.  Axioms and lemmas have type
   Tprop.  Finally, methods have type Tmeth {params; ret}.

   The translation from Ast.ty to ity depends on a typing
   environment G = (C, M) where C is the class table and M is a set of
   extern types (math types).
*)
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


(* -------------------------------------------------------------------------- *)
(* Utility functions on formulas and specs                                    *)
(* -------------------------------------------------------------------------- *)

let fconj_list = foldr1 (fun h t -> Fconn(Ast.Conj, h, t))

let fimp_list = foldr1 (fun h t -> Fconn(Ast.Imp, h, t))

let rconj_list = foldr1 (fun h t -> Rconn(Ast.Conj, h, t))

let rimp_list  = foldr1 (fun h t -> Rconn(Ast.Imp, h, t))

let spec_preconds (s: spec) : formula list =
  filtermap (function Precond f -> Some f | _ -> None) s

let spec_postconds (s: spec) : formula list =
  filtermap (function Postcond f -> Some f | _ -> None) s

let spec_effects (s: spec) : effect =
  concat_filter_map (function Effects e -> Some e | _ -> None) s

let bispec_preconds (s: bispec) : rformula list =
  filtermap (function Biprecond rf -> Some rf | _ -> None) s

let bispec_postconds (s: bispec) : rformula list =
  filtermap (function Bipostcond rf -> Some rf | _ -> None) s

let bispec_effects (s: bispec) : effect * effect =
  let es = filtermap (function Bieffects (e,e') -> Some (e,e') | _ -> None) s in
  map_pair flat (unzip es)

let mk_bispec_pre rf = Biprecond rf

let mk_bispec_post rf = Bipostcond rf


(* -------------------------------------------------------------------------- *)
(* Utility functions on predicates, lemmas, and axioms                        *)
(* -------------------------------------------------------------------------- *)

let is_private_inv nf = nf.annotation = Some Private_invariant
let is_public_inv nf = nf.annotation = Some Public_invariant
let is_coupling nrf = nrf.is_coupling

let named_formula_name nf =
  match nf.formula_name.node with
  | Id name -> name
  | _ -> failwith "named_formula_name"

let named_rformula_name nrf =
  match nrf.biformula_name with
  | Id name -> name
  | _ -> failwith "named_rformula_name"


(* -------------------------------------------------------------------------- *)
(* Utility functions on effects and boundaries                                *)
(* -------------------------------------------------------------------------- *)

let dest_eff e = (e.effect_kind, e.effect_desc)

let is_read e = e.effect_kind = Read
let is_write e = e.effect_kind = Write

let mk_eff_var k x =
  {effect_kind = k; effect_desc = Effvar x -: x.ty}

let mk_eff_img k g f =
  {effect_kind = k; effect_desc = Effimg (g,f) -: Trgn}

let rdvar x = mk_eff_var Read x

let wrvar x = mk_eff_var Write x

let rdimg g f = mk_eff_img Read g f

let wrimg g f = mk_eff_img Write g f

let is_eff_img (e: effect_desc t) =
  match e.node with
  | Effimg (_, _) -> true
  | _ -> false

let is_eff_var (e: effect_desc t) = not (is_eff_img e)

let is_rdvar e = is_eff_var e.effect_desc && is_read e

let is_rdimg e = is_eff_img e.effect_desc && is_read e

let is_wrvar e = is_eff_var e.effect_desc && is_write e

let is_wrimg e = is_eff_var e.effect_desc && is_write e

let sngl x = Esingleton (Evar x -: x.ty) -: Trgn

let rds, wrs = filter is_read, filter is_write

let r2w = map (fun e -> {e with effect_kind = Write}) % rds

let w2r = map (fun e -> {e with effect_kind = Read}) % wrs

(* Convert a boundary_decl to an effect *)
let eff_of_bnd (b: boundary_decl) : effect =
  map (fun e -> {effect_kind = Read; effect_desc = e}) b

(* Convert a list of (read) effects to a boundary  *)
let bnd_of_eff (eff: effect) : boundary_decl =
  let cons e es = match dest_eff e with
    | (Read, e') -> e' :: es
    | (Write, _) -> invalid_arg "bnd_of_eff" in
  foldr cons [] eff

(* bnd_plus bnd = bnd , alloc *)
let bnd_plus bnd : boundary_decl =
  let read_alloc = Effvar (Ast.Id "alloc" -: Trgn) -: Trgn in
  read_alloc :: bnd

(* Agreement on an effect *)
let agreement_list eff : rformula list =
  let rec aux frms = function
    | [] -> frms
    | {effect_kind = Write} :: es -> aux frms es
    | {effect_desc = desc} :: es ->
      let head = match desc.node with
        | Effvar x -> Rbiequal (Evar x -: x.ty, Evar x -: x.ty)
        | Effimg (g,f) -> Ragree (g,f) in
      aux (head :: frms) es
  in aux [] eff

let agreement_eff eff : rformula =
  if is_nil eff then Rboth Ftrue else rconj_list (agreement_list eff)

(* Normalize effects *)
module Norm : sig
  val normalize : effect -> effect
  val is_normalized : effect -> bool
end = struct

  type field_key = (ident t * effect_kind)

  module Ordered_field_key = struct
    type t = field_key
    let compare = compare
  end

  module M = Map.Make (Ordered_field_key)

  (* The property we want is: Normalize e = proj (emb e)
     where proj : emb -> effect and emb : effect -> emb.

     The imgs map associates a field name and an effect kind with a
     list of regions.  If an effect e contains rw {g}`f, {h}`f, wr {i}`f
     then (emb e).imgs contains:

       (f, Read) --> [{g}; {h}]  (f, Write) --> [{g}; {h}; {i}]

     When converting back, we get the effect:

       rd ({g} union {h})`f, wr ({g} union {h} union {i})`f

     Each list of regions is union'd, and the effect kind is used to
     recover the type of effect.
  *)
  type emb = { imgs: exp t list M.t; vars: (ident t * ity * effect_kind) list }

  let mk_union r r' : exp t =
    match r.node, r'.node with
    | Econst {node = Eemptyset; _}, _ -> r'
    | _, Econst {node = Eemptyset; _} -> r
    | _, _ -> Ebinop (Union, r, r') -: Trgn

  let mk_union_list regions = foldl1 mk_union regions

  let emb (eff: effect) : emb =
    let rec walk imgs vars eff =
      match eff with
      | [] -> {imgs; vars}
      | e::es ->
        match e.effect_desc.node with
        | Effimg (g,f) ->
          let key = (f, e.effect_kind) in
          let imgs' = M.update key (function
              | None -> Some [g]
              | Some gs -> Some (g::gs)
            ) imgs in
          walk imgs' vars es
        | Effvar x ->
          walk imgs ((x, e.effect_desc.ty, e.effect_kind) :: vars) es
    in walk M.empty [] eff

  let proj {imgs; vars} : effect =
    let img_effs =
      M.fold (fun (fld, eff_kind) regions effects ->
          assert (length regions >= 1);
          let combined = mk_union_list regions in
          let desc = Effimg (combined, fld) -: Trgn in
          let eff = {effect_kind = eff_kind; effect_desc = desc} in
          eff :: effects
        ) imgs [] in
    let var_effs =
      foldr (fun (x, xty, eff_kind) effects ->
          let desc = Effvar x -: xty in
          let eff = {effect_kind = eff_kind; effect_desc = desc} in
          eff :: effects
        ) [] vars
    in
    img_effs @ var_effs

  let is_normalized eff =
    let get eff = map (fun e -> e.effect_desc.node -: Trgn) eff in
    let imgs eff = map (fun e -> e.node) (filter is_eff_img (get eff)) in
    let fld = function Effimg (_,f) -> f.node | _ -> invalid_arg "fld" in
    let wrs = wrs eff and rds = rds eff in
    let wrs_imgs = imgs wrs and rds_imgs = imgs rds in
    is_unique (map fld wrs_imgs) && is_unique (map fld rds_imgs)

  let normalize eff = if is_normalized eff then eff else proj (emb eff)

end

let normalize_boundary = bnd_of_eff % Norm.normalize % eff_of_bnd

let is_normalized_boundary = Norm.is_normalized % eff_of_bnd

(* subtract e1 e2 = d1 @ d2 @ d3 @ d4 where

   d1 = [ rd x   | rd x in e1 and rd x notin e2 ]
   d2 = [ rd G`f | rd G`f in e1 and e2 has no f read ]
      @ [ rd (G\H)`f | rd G`f in e1 and rd H`f in e2 ]

   d3 and d4 are similarly defined for writes.  e1 and e2 are
   normalized first.
*)
let subtract e1 e2 : effect =
  let e1, e2 = map_pair Norm.normalize (e1, e2) in
  let find_img fld knd eff =
    List.find_opt (fun e ->
        match e.effect_desc.node with
        | Effimg (g,f) -> fld = f.node && knd = e.effect_kind
        | _ -> false
      ) eff in
  let sub eff acc = match eff.effect_desc with
    | {node = Effvar x} -> if mem eff e2 then acc else eff :: acc
    | {node = Effimg (g,f)} ->
      match find_img f.node eff.effect_kind e2 with
      | None -> eff :: acc
      | Some {effect_desc = {node = Effimg (h, _); ty}} ->
        let rgn = Ebinop (Ast.Diff, g, h) -: Trgn in
        let eff = {eff with effect_desc = Effimg (rgn,f) -: ty} in
        eff :: acc
      | _ -> assert false
  in
  foldr sub [] e1

(* combine_effect e1 e2 = e

   e is e1 @ e2, but is normalized and does not contain duplicates.
*)
let combine_effect e1 e2 = nub (Norm.normalize (e1 @ e2))

(* snap and Asnap *)
module Snap : sig
  type snapshot
  val mk_snapshot_ident : exp t -> unit -> ident
  val snap : effect -> snapshot
  val asnap : snapshot -> effect -> effect
  val asnap' : effect -> effect
  val close : snapshot -> rformula -> rformula
  val close_quantify : snapshot -> rformula -> rformula
end = struct

  (* A snapshot is a map from region expressions to identifiers.

     In our syntax, old(e) is not an expression.  The only way to refer to the
     old value of e is to assert x = old(e) or bind old(e) in a formula,
     e.g. let e' = old(e) in P(e').  In relation formulas, we may say
     let e'|e' = old(e)|old(e) in \R(e').

     Given a snapshot S and a relation formula P(xs) with free variables xs in
     rng(S), we may construct a closed relation formula P' by binding each x in
     xs to the old value of e where (e,x) in S.

     Example:

     if S = [f |-> s1; h union g |-> s2] then P':

       let s1|s1 = old(f)|old(f) in
       let s2|s2 = old(h union g)|old(h union g) in
       P(s1,s2)
  *)

  module ExpM = (val mk_map compare : Map.S with type key = exp t)

  type snapshot = ident ExpM.t
  type rf_ctx = (rformula -> rformula)

  let rf_ctx_of_snapshot (s: snapshot) : rf_ctx =
    let bind_in_let rgn name frm =
      let ty = rgn.ty in
      let lbind = {value=Lexp rgn -: ty; is_old=true; is_init=false} -: ty in
      let rbind = {value=Lexp rgn -: ty; is_old=true; is_init=false} -: ty in
      Rlet (Some (name -: ty, ty, lbind), Some (name -: ty, ty, rbind), frm)
    in
    ExpM.fold bind_in_let s

  let close s rf : rformula = rf_ctx_of_snapshot s rf

  (* Like close but universally quantifiers over snapshot variables instead of
     binding them in a let.  Loses information about the snapshot expression. *)
  let close_quantify (s: snapshot) rf : rformula =
    let mk_rqbinders rgn name (lbinds,rbinds) =
      let ty = rgn.ty in
      let lbind = {name = name -: ty; in_rgn = None; is_non_null = false} in
      let rbind = {name = name -: ty; in_rgn = None; is_non_null = false} in
      (lbind :: lbinds, rbind :: rbinds) in
    let rqbinders = ExpM.fold mk_rqbinders s ([],[]) in
    if rqbinders = ([],[]) then rf else Rquant(Ast.Forall, rqbinders, rf)

  (* mk_snapshot_ident G () = id

     id is an appropriately named identifier for G.

     FIXME: There may be name clashes if a user defines an identifier with the
     same name we generate.  To test.
  *)
  let mk_snapshot_ident : exp t -> unit -> ident =
    let id name = Ast.Id name in
    let create_name e =
      match e.node with
      | Evar {node = Id "alloc"; _} -> "s_alloc"
      | Evar {node = Id name; _} -> name
      | Esingleton {node = Evar {node = Id name; _}; _} -> name
      | Eimage (g, {node = Id f; _}) -> f
      | _ -> "snap_r" in
    let stamp = ref 0 in
    let names = ref [] in
    fun rgn () -> begin
        let oldstamp = !stamp in
        incr stamp;
        let name = ref (create_name rgn ^ string_of_int oldstamp) in
        while mem name !names do
          incr stamp;
          name := create_name rgn ^ string_of_int !stamp
        done;
        names := name :: !names;
        id !name
      end

  (* snap e = S

     Computes snap as defined in the paper (Def 8.2), but returns a
     snapshot instead of of a unary formula.

     Invariant:
     For each s_G,f = G derived by snap in the logic, S contains a
     the mapping G |-> s_G,f
  *)
  let snap e : snapshot =
    let walk e acc = match e with
      | {effect_kind = Read} -> acc
      | {effect_desc = desc} ->  (* write effects only *)
        match desc.node with
        | Effvar _ -> acc
        | Effimg (g,f) ->
          let name = mk_snapshot_ident g () in
          ExpM.add g name acc
    in
    foldl walk ExpM.empty e

  (* asnap S e = e'

     Given a snapshot S and an effect e, computes a read effect e' (Def 8.2).

     Invariant:
     If S = snap(e) then
       for each (wr G`f) in e, e' contains rd (s_G,f)`f
         where (G |-> s_G,f) in S.
       for each (wr x) in e, e' contains rd x iff x <> alloc
       length(e') = length(wrs(e)) - # of wr alloc's in e
  *)
  let asnap s e =
    let walk = function
      | {effect_kind = Read} -> []
      | {effect_desc = desc} ->
        match desc.node with
        | Effvar x -> if x.node <> Ast.Id "alloc" then [rdvar x] else []
        | Effimg (g,f) ->
          let name = ExpM.find g s in
          let var = Evar (name -: g.ty) -: g.ty in
          [rdimg var f]
    in concat_map walk e

  let asnap' e = asnap (snap e) e

end

(* agreement_effpre eff bnd = Agree (eff \ (bnd, rd alloc)) *)
let agreement_effpre eff bnd : rformula list =
  agreement_list (subtract (rds eff) (eff_of_bnd (bnd_plus bnd)))

(* agreement_effpost ?quantify eff bnd = Agree (effpost (eff, bnd))

   where effpost (eff, bnd) = (rd (alloc \ s_alloc)`any, Asnap(eff)) \ bnd
         s_alloc snapshots alloc

   Invariant:
     if quantify = true the result is a closed rformula of the form:
       forall s_alloc:rgn|s_alloc:rgn. ...
     and all snapshot variables are universally quantified.

     otherwise the result is a closed rformula of the form:
       let s_alloc|s_alloc = old(alloc)|old(alloc) in
       ...
     and all snapshot variables are bound in a let.

  [Sep-30-22]
  agreement_effpost ?quantify fields eff bnd = Agree (effpost (eff, bnd))

  Functions the same as the previous version, but additionally fields is used
  to resolve datagroup "any" in (alloc \ s_alloc)`any.  Here, fields is meant
  to be a list of all known fields.
 *)
let agreement_effpost ?(quantify=false) fields eff bnd : rformula =
  (* [Sep-30-22] TODO: duplicated in pretrans/resolve_datagroups.ml.  This
     suggests resolve_effect should be a separate toplevel function in this
     file.  Note that pretrans/resolve_datagroups.ml was written before
     resolve_effect was added here. *)
  let resolve_effect es =
    let resolve k t g f = {effect_kind = k; effect_desc = Effimg (g,f) -: t} in
    let walk ({effect_kind = k; effect_desc=eff} as e) =
      match eff.node with
      | Effimg (g, f) when f.node = Id "any" -> map (resolve k eff.ty g) fields
      | _ -> [e] in
    concat_map walk es in
  let eff = Norm.normalize eff in
  let bnd = Norm.normalize (eff_of_bnd bnd) in
  let alloc = Evar (Ast.Id "alloc" -: Trgn) -: Trgn in
  let s_alloc_id = Snap.mk_snapshot_ident alloc () -: Trgn in
  let s_alloc = Evar s_alloc_id -: Trgn in
  let alloc_diff = Ebinop (Ast.Diff, alloc, s_alloc) -: Trgn in
  let alloc_diff_eff = [rdimg alloc_diff (Ast.Id "any" -: Tdatagroup)] in
  let alloc_diff_eff = resolve_effect alloc_diff_eff in
  let oalloc = {value = Lexp alloc -: Trgn; is_old = true; is_init = false} in
  let snapshot = Snap.snap eff in
  let asnap_eff = Snap.asnap snapshot eff in
  let effpost = subtract (combine_effect alloc_diff_eff asnap_eff) bnd in
  if not quantify then
    let oalloc_lb = (s_alloc_id, Trgn, oalloc -: Trgn) in
    Rlet (Some oalloc_lb, Some oalloc_lb,
          Snap.close snapshot (agreement_eff effpost))
  else
    let binder = {name = s_alloc_id; in_rgn = None; is_non_null = false} in
    let inner = Snap.close_quantify snapshot (agreement_eff effpost) in
    Rquant (Ast.Forall, ([binder],[binder]), inner)

(* -------------------------------------------------------------------------- *)
(* Footprints of expressions and formulas                                     *)
(* -------------------------------------------------------------------------- *)

(* Footprint of an expression *)
(* [Sep-26-2022] Initially ftpt(x) where x is a variable was just (rd x).
   Update rule to now handle variables of math/extern type: ftpt(x) where x is
   of math type is just the empty read effect. *)
let ftpt_exp (e: exp t) : effect =
  let rec aux eff e = match e.node with
    | Econst _ -> eff
    | Evar x -> begin match e.ty with
      | Tmath(_,_) -> eff
      | _ -> rdvar x :: eff
      end
    | Ebinop (_, e1, e2) -> aux (aux eff e1) e2
    | Eunrop (_, e) -> aux eff e
    | Esingleton e -> aux eff e
    | Eimage (g, f) -> aux (rdimg g f :: eff) g
    | Esubrgn (g, k) -> aux eff g (* CHECK *)
    | Ecall (m, es) -> List.fold_left aux eff es
    | Einit e -> aux eff e in
  aux [] e

(* Footprint of a let_bound_value *)
let ftpt_lb (lb: let_bound_value t) : effect =
  match lb.node with
  | Lloc (x, f) -> [rdvar x; rdimg (sngl x) f]
  | Larr (a, i) -> [rdvar a]
  | Lexp e -> ftpt_exp e

(* Footprint of a formula *)
(* FIXME: Review ftpt(a[i]=e)--should probably read the slots field as well, but
   we need the class table to figure out the name of the slots field. *)
let ftpt_formula (f: formula) : effect =
  let rec aux eff = function
    | Ftrue | Ffalse -> eff
    | Fexp e -> ftpt_exp e @ eff
    | Finit lb -> ftpt_lb lb @ eff
    | Fnot f -> aux eff f
    | Fpointsto (x, f, e) -> rdvar x :: rdimg (sngl x) f :: ftpt_exp e @ eff
    | Farray_pointsto (a, i, e) -> rdvar a :: ftpt_exp e @ eff
    | Fmember (e1, e2) -> ftpt_exp e1 @ ftpt_exp e2 @ eff
    | Fsubseteq (e1, e2) -> ftpt_exp e1 @ ftpt_exp e2 @ eff
    | Fdisjoint (e1, e2) -> ftpt_exp e1 @ ftpt_exp e2 @ eff
    | Flet (x, lb, f) -> aux (rdvar x :: ftpt_lb lb.node.value @ eff) f
    | Fconn (_, f1, f2) -> aux (aux eff f1) f2
    | Fquant _ -> invalid_arg "ftpt_formula: expected an atomic formula"
    | Fold (e, lb) -> ftpt_exp e @ ftpt_lb lb @ eff
    | Ftype (e, _) -> ftpt_exp e @ eff in
  aux [] f


(* -------------------------------------------------------------------------- *)
(* Functions that deal with free variables                                    *)
(* -------------------------------------------------------------------------- *)

(* Set of identifiers *)
module IdS = Astutil.S

let free_vars_exp e =
  let rec aux fv e = match e.node with
    | Econst _ -> fv
    | Evar x -> IdS.add x.node fv
    | Ebinop (_, e1, e2) -> aux (aux fv e1) e2
    | Eunrop (_, e) -> aux fv e
    | Esingleton e -> aux fv e
    | Eimage (g, f) -> (* aux (IdS.add f.node fv) g *) aux fv g
    | Esubrgn (g, k) -> aux fv g
    | Ecall (id, es) -> List.fold_left aux (IdS.add id.node fv) es
    | Einit e -> aux fv e in
  aux IdS.empty e

let free_vars_exp_opt = function
  | None -> IdS.empty
  | Some e -> free_vars_exp e

let free_vars_let_bound_value = function
  | Lloc (x, f) -> IdS.of_list [x.node; f.node]
  | Larr (a, i) -> IdS.add a.node (free_vars_exp i)
  | Lexp e -> free_vars_exp e

let rec free_vars_formula f = match f with
  | Ftrue | Ffalse -> IdS.empty
  | Finit e -> free_vars_let_bound_value e.node
  | Fexp e -> free_vars_exp e
  | Fnot f -> free_vars_formula f
  | Fpointsto (x, f, e) ->
    let s = IdS.of_list [x.node; f.node] in
    IdS.union s (free_vars_exp e)
  | Farray_pointsto (a, i, e) ->
    IdS.add a.node (IdS.union (free_vars_exp i) (free_vars_exp e))
  | Fsubseteq (e1, e2) | Fdisjoint (e1, e2)
  | Fmember (e1, e2) -> IdS.union (free_vars_exp e1) (free_vars_exp e2)
  | Flet (x, {node={value=lb; _}; _}, f) ->
    let lb_fv = free_vars_let_bound_value lb.node in
    let f_fv  = free_vars_formula f in
    IdS.union lb_fv (IdS.diff f_fv (IdS.singleton x.node))
  | Fconn (_, f1, f2) -> IdS.union (free_vars_formula f1) (free_vars_formula f2)
  | Fquant (q, qbinds, f) ->
    let f_fv = free_vars_formula f in
    let bind_names = map (fun x -> x.name.node) qbinds in
    let es_fv = map (function {in_rgn} -> free_vars_exp_opt in_rgn) qbinds in
    let es_fv = List.fold_left IdS.union IdS.empty es_fv in
    IdS.union es_fv (IdS.diff f_fv (IdS.of_list bind_names))
  | Fold (e, {node=lb; _}) ->
    IdS.union (free_vars_exp e) (free_vars_let_bound_value lb)
  | Ftype (e, k) -> free_vars_exp e

let free_vars_effect_desc = function
  | Effvar x -> IdS.singleton x.node
  | Effimg (e,_) -> free_vars_exp e

let free_vars_effect_elt e = free_vars_effect_desc e.effect_desc.node

let rec free_vars_effect = function
  | [] -> IdS.empty
  | e :: es -> IdS.union (free_vars_effect_elt e) (free_vars_effect es)

let rec free_vars_value_in_state = function
  | Left e | Right e -> free_vars_exp e

let rec free_vars_bexp = function
  | Bibinop (_, e1, e2) ->
    IdS.union (free_vars_bexp e1.node) (free_vars_bexp e2.node)
  | Biconst c -> free_vars_exp (Econst c -: c.ty)
  | Bivalue v -> free_vars_value_in_state v.node

let rec free_vars_rformula = function
  | Rprimitive {name=m; left_args; right_args} ->
    let lfree = List.map free_vars_exp left_args in
    let rfree = List.map free_vars_exp right_args in
    (IdS.add m (foldl IdS.union IdS.empty lfree),
     IdS.add m (foldl IdS.union IdS.empty rfree))
  | Rbiexp bexp -> dup_pair @@ free_vars_bexp bexp.node
  | Rbiequal (e, e') -> (free_vars_exp e, free_vars_exp e')
  | Ragree (e, f) -> dup_pair @@ IdS.add f.node (free_vars_exp e)
  | Rboth f -> dup_pair @@ free_vars_formula f
  | Rleft f -> (free_vars_formula f, IdS.empty)
  | Rright f -> (IdS.empty, free_vars_formula f)
  | Rnot rf -> free_vars_rformula rf
  | Rlater rf -> free_vars_rformula rf
  | Rconn (_, rf1, rf2) ->
    let (lfree1, rfree1) = free_vars_rformula rf1 in
    let (lfree2, rfree2) = free_vars_rformula rf2 in
    (IdS.union lfree1 lfree2, IdS.union rfree1 rfree2)
  | Rquant (q, (lbinds, rbinds), rf) ->
    let (lfree, rfree) = free_vars_rformula rf in
    let lnames = map (function {name} -> name.node) lbinds in
    let rnames = map (function {name} -> name.node) rbinds in
    let lexps = map (function {in_rgn} -> free_vars_exp_opt in_rgn) lbinds in
    let rexps = map (function {in_rgn} -> free_vars_exp_opt in_rgn) rbinds in
    let lexp_fvs = foldl IdS.union IdS.empty lexps
    and rexp_fvs = foldl IdS.union IdS.empty rexps in
    (IdS.union lexp_fvs (IdS.diff lfree (IdS.of_list lnames)),
     IdS.union rexp_fvs (IdS.diff rfree (IdS.of_list rnames)))
  | Rlet (Some (lid, _, {node={value=llb; _};_}),
          Some (rid, _, {node={value=rlb; _};_}), rf) ->
    let (lfree, rfree) = free_vars_rformula rf in
    let llb_fv = free_vars_let_bound_value llb.node in
    let rlb_fv = free_vars_let_bound_value rlb.node in
    (IdS.remove lid.node (IdS.union llb_fv lfree),
     IdS.remove rid.node (IdS.union rlb_fv rfree))
  | Rlet (Some (lid, _, {node={value=llb; _}; _}), None, rf) ->
    let (lfree, rfree) = free_vars_rformula rf in
    let llb_fv = free_vars_let_bound_value llb.node in
    (IdS.remove lid.node (IdS.union llb_fv lfree), rfree)
  | Rlet (None, Some (rid, _, {node={value=rlb; _}; _}), rf) ->
    let (lfree, rfree) = free_vars_rformula rf in
    let rlb_fv = free_vars_let_bound_value rlb.node in
    (lfree, IdS.remove rid.node (IdS.union rlb_fv lfree))
  | Rlet (None, None, rf) -> assert false (* impossible *)

(* -------------------------------------------------------------------------- *)
(* Simplifications and rewritings                                             *)
(* -------------------------------------------------------------------------- *)

(* reassoc f = f'

   any subterm in f of the form f1 /\ f2 /\ f3 is rewritten to
   (f1 /\ f2) /\ f3 in f'.
*)
let rec reassoc (f: formula) : formula =
  match f with
  | Fconn (Conj, f1, f2) ->
    let f1' = reassoc f1 in
    let f2' = reassoc f2 in
    begin match f2' with
      | Fconn (Conj, t1, t2) -> Fconn (Conj, Fconn (Conj, f1', t1), t2)
      | _ -> Fconn (Conj, f1', f2')
    end
  | Fnot f -> Fnot (reassoc f)
  | Flet (id, v, f) -> Flet (id, v, reassoc f)
  | Fconn (c, f1, f2) -> Fconn (c, reassoc f1, reassoc f2)
  | Fquant (q, qbinds, f) -> Fquant (q, qbinds, reassoc f)
  | _ -> f

(* simplify_formula f = f'

   rewrite every occurence of true /\ H or H /\ true in f to H in f'.
*)
let rec simplify_formula (f: formula) : formula =
  match f with
  | Ftrue -> Ftrue
  (* FIXME: Using builtin equality below *)
  | Fexp {node=Ebinop (Equal, e1, e2); _} when e1 = e2 -> Ftrue
  | Fconn (Conj, f1, f2) ->
    let f1' = simplify_formula f1 in
    let f2' = simplify_formula f2 in
    begin match f1', f2' with
      | Ftrue, h
      | h, Ftrue
      | Fexp {node=Econst {node=Ebool true; _};_}, h
      | h, Fexp {node=Econst {node=Ebool true; _};_} -> h
      | _, _ -> Fconn (Conj, f1', f2')
    end
  | Fnot f -> Fnot (simplify_formula f)
  | Flet (id, v, f) -> Flet (id, v, simplify_formula f)
  | Fconn (c, f1, f2) -> Fconn (c, simplify_formula f1, simplify_formula f2)
  | Fquant (q, qbinds, f) -> Fquant (q, qbinds, simplify_formula f)
  | _ -> f

(* rw_skip c = c'

   Rewrite rules:

     skip; d --> skip; d            d; skip --> skip; d

     c; (skip; d) --> skip; (c; d)  c; (d; skip) --> skip; (c; d)

     (skip; c); d --> skip; (c; d)  (c; skip); d --> skip; (c; d)

*)
let rec rw_skip (c: command) : command =
  match c with
  | Acommand ac -> Acommand ac
  | Vardecl (id, modif, ty, c) -> Vardecl (id, modif, ty, rw_skip c)
  | Seq (c1, c2) ->
    let c1' = rw_skip c1 in
    let c2' = rw_skip c2 in
    begin match c1', c2' with
      | Acommand Skip, d | d, Acommand Skip -> Seq (Acommand Skip, d)
      | _, Seq (Acommand Skip, d) | _, Seq (d, Acommand Skip) ->
        Seq (Acommand Skip, Seq (c1', d))
      | Seq (Acommand Skip, d), _ | Seq (d, Acommand Skip), _ ->
        Seq (Acommand Skip, Seq (d, c2'))
      | _, _ -> Seq (c1', c2')
    end
  | If (e, c1, c2) -> If (e, rw_skip c1, rw_skip c2)
  | While (e, f, c) -> While (e, f, rw_skip c)
  | _ -> c


(* simplify_command c = c'

   rewrite every occurence of skip ; D or D ; skip in c to D in c';
   rewrite assert { f } and assume { f } in c to skip in c';
   rewrite while false do C done to skip
*)
let rec simplify_command (c: command) : command =
  match c with
  | Acommand ac -> Acommand ac
  | Vardecl (id, modif, ty, c) -> Vardecl (id, modif, ty, simplify_command c)
  | Seq (c1, c2) ->
    let c1' = simplify_command c1 in
    let c2' = simplify_command c2 in
    begin match c1', c2' with
      | Acommand Skip, d | d, Acommand Skip -> d
      | _, _ -> Seq (c1', c2')
    end
  | If (e, c1, c2) -> If (e, simplify_command c1, simplify_command c2)
  | While ({node=Econst {node=Ebool false}}, _, _) -> Acommand Skip
  | While (e, {winvariants; wframe; wvariant}, c) ->
    let winvariants = map simplify_formula winvariants in
    While (e, {winvariants; wframe; wvariant}, simplify_command c)
  | Assume _ | Assert _ -> Acommand Skip

(* rewrite ((c1 ; c2) ; c3) to (c1 ; (c2 ; c3)) *)
let rec reassoc_command (c: command) : command =
  match c with
  | Seq (c1, c2) ->
    let c1' = reassoc_command c1 in
    let c2' = reassoc_command c2 in
    begin match c1' with
      | Seq (c1, c2) -> Seq (c1, reassoc_command (Seq (c2, c2')))
      | _ -> Seq (c1', c2')
    end
  | Vardecl (id, modif, ty, c) -> Vardecl (id, modif, ty, reassoc_command c)
  | If (e, c1, c2) -> If (e, reassoc_command c1, reassoc_command c2)
  | While (e, f, c) -> While (e, f, reassoc_command c)
  | c -> c

let rw_command = reassoc_command % simplify_command % rw_skip


(* -------------------------------------------------------------------------- *)
(* Equality mod assertions/assumptions/invariants/extra locals                *)
(* -------------------------------------------------------------------------- *)

let rec eqv_command c c' = match c, c' with
  | Acommand ac, Acommand ac' -> ac = ac'
  | Vardecl (id, m, ty, c), Vardecl (id', m', ty', c') ->
    eqv_command c c'
    (* id = id' && m = m' && ty = ty' && eqv_command c c' *)
  | Vardecl (id, m, ty, c), c' -> eqv_command c c'
  | c, Vardecl (id, m, ty, c') -> eqv_command c c'
  | Seq (c1, c2), Seq (c1', c2') -> eqv_command c1 c1' && eqv_command c2 c2'
  | If (e, c1, c2), If (e', c1', c2') ->
    e = e' && eqv_command c1 c1' && eqv_command c2 c2'
  | While (e, _, c), While (e', _, c') -> e = e' && eqv_command c c'
  | Assume _, Assume _ -> true
  | Assert _, Assert _ -> true
  | _, _ -> false


(* -------------------------------------------------------------------------- *)
(* Functions on biprograms and projections                                    *)
(* -------------------------------------------------------------------------- *)

let mk_seq xs = foldr1 (fun x y -> Seq(x,y)) xs

let mk_biseq xs = foldr1 (fun x y -> Biseq(x,y)) xs

let map_fourwayif f {then_then; then_else; else_then; else_else} =
  {then_then = f then_then; then_else = f then_else;
   else_then = f else_then; else_else = f else_else}

let rec does_biupdate = function
  | Bihavoc_right _ -> false
  | Biupdate (_, _) -> true
  | Bisplit _ | Bisync _ | Biassume _ | Biassert _ -> false
  | Bivardecl (_, _, cc) | Biwhile (_, _, _, _, cc) ->
    does_biupdate cc
  | Biseq (cc1, cc2) | Biif (_, _, cc1, cc2) ->
    does_biupdate cc1 || does_biupdate cc2
  | Biif4 (_, _, {then_then; then_else; else_then; else_else}) ->
    does_biupdate then_then ||
    does_biupdate then_else ||
    does_biupdate else_then ||
    does_biupdate else_else

let rec reassoc_bicommand (cc: bicommand) : bicommand =
  match cc with
  | Biseq (cc1, cc2) ->
    let cc1' = reassoc_bicommand cc1 in
    let cc2' = reassoc_bicommand cc2 in
    begin match cc1' with
      | Biseq (cc1, cc2) -> Biseq (cc1, reassoc_bicommand (Biseq (cc2, cc2')))
      | _ -> Biseq (cc1', cc2')
    end
  | Bisplit (c1, c2) -> Bisplit (reassoc_command c1, reassoc_command c2)
  | Bivardecl (x, y, cc) -> Bivardecl (x, y, reassoc_bicommand cc)
  | Biif (e, e', cc1, cc2) ->
    Biif (e, e', reassoc_bicommand cc1, reassoc_bicommand cc2)
  | Biif4 (e, e', branches) ->
    Biif4 (e, e', map_fourwayif reassoc_bicommand branches)
  | Biwhile (e, e', ag, ws, cc) -> Biwhile (e, e', ag, ws, reassoc_bicommand cc)
  | c -> c

let projl_biexp (b: biexp t) : formula =
  let open Option.Monad_syntax in
  let rec projl b : exp t option = match b.node with
    | Bivalue {node = Left e} -> Some e
    | Bivalue {node = Right e} -> None
    | Bibinop (op, e1, e2) ->
      let* e1 = projl e1 in
      let* e2 = projl e2 in
      Some (Ebinop (op, e1, e2) -: b.ty)
    | Biconst c -> Some (Econst c -: c.ty)
  in try Fexp (Option.get (projl b)) with _ -> Ftrue

let projr_biexp (b: biexp t) : formula =
  let open Option.Monad_syntax in
  let rec projr b : exp t option = match b.node with
    | Bivalue {node = Left e} -> None
    | Bivalue {node = Right e} -> Some e
    | Bibinop (op, e1, e2) ->
      let* e1 = projr e1 in
      let* e2 = projr e2 in
      Some (Ebinop (op,e1,e2) -: b.ty)
    | Biconst c -> Some (Econst c -: c.ty)
  in try Fexp (Option.get (projr b)) with _ -> Ftrue

let rec projl_rformula (rf: rformula) : formula =
  match rf with
  | Rprimitive _ | Rright _ -> Ftrue
  | Rleft f | Rboth f -> f
  | Rbiexp b -> projl_biexp b
  | Rnot rf -> Fnot (projl_rformula rf)
  | Rbiequal (e, _) -> Fexp (Ebinop (Equal, e, e) -: Tbool)
  | Ragree (g, f) ->
    let img_exp = Eimage (g, f) -: Trgn in
    let equal_exp = Ebinop (Equal, img_exp, img_exp) in
    Fexp (equal_exp -: Tbool)
  | Rconn (c, rf1, rf2) -> Fconn (c, projl_rformula rf1, projl_rformula rf2)
  | Rquant (q, (bindings, _), rf) -> Fquant (q, bindings, projl_rformula rf)
  | Rlet (Some (x, _, xval), _, rf) -> Flet (x, xval, projl_rformula rf)
  | Rlet (None, _, rf) -> projl_rformula rf
  | Rlater rf -> projl_rformula rf

let rec projr_rformula (rf: rformula) : formula =
  match rf with
  | Rprimitive _ | Rleft _ -> Ftrue
  | Rright f | Rboth f -> f
  | Rbiexp b -> projr_biexp b
  | Rnot rf -> Fnot (projr_rformula rf)
  | Rbiequal (_, e) -> Fexp (Ebinop (Equal, e, e) -: Tbool)
  | Ragree (g, f) ->
    let img_exp = Eimage (g, f) -: Trgn in
    let equal_exp = Ebinop (Equal, img_exp, img_exp) in
    Fexp (equal_exp -: Tbool)
  | Rconn (c, rf1, rf2) -> Fconn (c, projr_rformula rf1, projr_rformula rf2)
  | Rquant (q, (_, bindings), rf) -> Fquant (q, bindings, projr_rformula rf)
  | Rlet (_, Some (x, _, xval), rf) -> Flet (x, xval, projr_rformula rf)
  | Rlet (_, None, rf) -> projr_rformula rf
  | Rlater rf -> projr_rformula rf

let rec projl (cc: bicommand) : command =
  match cc with
  | Bihavoc_right (x, _) -> Acommand Skip
  | Bisplit (cl, _) -> cl
  | Bisync ac -> Acommand ac
  | Biseq (cc1, cc2) -> Seq (projl cc1, projl cc2)
  | Bivardecl (Some (id, modif, ty), _, cc) -> Vardecl (id, modif, ty, projl cc)
  | Bivardecl (None, _, cc) -> projl cc
  | Biif (e, _, cc1, cc2) -> If (e, projl cc1, projl cc2)
  | Biif4 (e, _, {then_then; then_else; else_then; else_else}) ->
    let then1, else1 = projl then_then, projl else_then in
    (* let then2, else2 = projl then_else, projl else_else in *)
    (* assert (eqv_command (rw_command then1) (rw_command then2)); *)
    (* assert (eqv_command (rw_command else1) (rw_command else2)); *)
    If (e, then1, else1)
  | Biwhile (e, _, _, {biwinvariants; biwframe=(eff, _); biwvariant}, cc) ->
    let winvariants = map projl_rformula biwinvariants in
    While (e, {winvariants; wframe=eff; wvariant=None}, projl cc)
  | Biassume rf -> (* Assume (projl_rformula rf) *) Acommand Skip
  | Biassert rf -> (* Assert (projl_rformula rf) *) Acommand Skip
  | Biupdate _ -> Acommand Skip

let rec projr (cc: bicommand) : command =
  match cc with
  | Bihavoc_right (x, _) -> Acommand (Havoc x)
  | Bisplit (_, cr) -> cr
  | Bisync ac -> Acommand ac
  | Biseq (cc1, cc2) -> Seq (projr cc1, projr cc2)
  | Bivardecl (_, Some (id, modif, ty), cc) -> Vardecl (id, modif, ty, projr cc)
  | Bivardecl (_, None, cc) -> projr cc
  | Biif (_, e, cc1, cc2) -> If (e, projr cc1, projr cc2)
  | Biif4 (_, e, {then_then; then_else; else_then; else_else}) ->
    let then1, else1 = projr then_then, projr then_else in
    (* let then2, else2 = projr else_then, projr else_else in *)
    (* assert (eqv_command (rw_command then1) (rw_command then2)); *)
    (* assert (eqv_command (rw_command else1) (rw_command else2)); *)
    If (e, then1, else1)
  | Biwhile (_, e, _, {biwinvariants; biwframe=(_,eff)}, cc) ->
    let winvariants = map projr_rformula biwinvariants in
    While (e, {winvariants; wframe=eff; wvariant=None}, projr cc)
  | Biassume rf -> (* Assume (projr_rformula rf) *) Acommand Skip
  | Biassert rf -> (* Assert (projr_rformula rf) *) Acommand Skip
  | Biupdate _ -> Acommand Skip

let rec projr_bicommand (cc: bicommand) : bicommand =
  match cc with
  | Bihavoc_right (x, rf) -> Bihavoc_right (x, rf)
  | Bisplit (_, cr) -> Bisplit (Acommand Skip, cr)
  | Bisync ac -> Bisplit (Acommand Skip, Acommand ac)
  | Biassume rf -> Biassume rf
  | Biassert rf -> Biassert rf
  | Biupdate (x, x') -> Biupdate (x, x')
  | Biseq (cc1, cc2) -> Biseq (projr_bicommand cc1, projr_bicommand cc2)
  | Bivardecl (_, Some v, cc) -> Bivardecl (None, Some v, projr_bicommand cc)
  | Bivardecl (_, None, cc) -> projr_bicommand cc
  | Biif (_, e, cc1, cc2) ->
    let true_exp = Econst (Ebool true -: Tbool) -: Tbool in
    let cc1' = projr_bicommand cc1 in
    let cc2' = projr_bicommand cc2 in
    let branches = { then_then = cc1'; then_else = cc2';
                     else_then = cc1'; else_else = cc2' } in
    Biif4 (true_exp, e, branches)
  | Biif4 (_, e, branches) ->
    let true_exp = Econst (Ebool true -: Tbool) -: Tbool in
    let branches' = map_fourwayif projr_bicommand branches in
    Biif4 (true_exp, e, branches')
  | Biwhile (_, e, _, {biwinvariants; biwvariant; biwframe=(_,eff)}, cc) ->
    let false_exp = Econst (Ebool false -: Tbool) -: Tbool in
    let ag = (Rleft Ffalse, Rright Ftrue) in
    let cc' = projr_bicommand cc in
    let biwframe = ([], eff) in
    Biwhile (false_exp, e, ag, {biwinvariants; biwvariant; biwframe}, cc')

(* Source programs are not allowed to have vars that start with this prefix. *)
let reserved_id_prefix = "q__"

let mk_fresh_id : string -> ident =
  let c = ref 0 in
  fun name -> incr c; Id (reserved_id_prefix ^ name ^ Int.to_string !c)

and is_false_ag (f: rformula) = match f with
  | Rleft Ffalse | Rright Ffalse | Rboth Ffalse -> true
  | _ -> false

let projl_rformula_simplify (rf: rformula) : formula =
  let f = projl_rformula rf in
  simplify_formula (reassoc f)

let projr_rformula_simplify (rf: rformula) : formula =
  let f = projr_rformula rf in
  simplify_formula (reassoc f)

let projl_simplify (cc: bicommand) : command =
  let c = projl cc in
  reassoc_command @@ simplify_command (rw_skip c)

let projr_simplify (cc: bicommand) : command =
  let c = projr cc in
  reassoc_command @@ simplify_command (rw_skip c)


(* -------------------------------------------------------------------------- *)
(* Utility functions on program_elts and penvs                                *)
(* -------------------------------------------------------------------------- *)

let mk_import import_kind import_name related_by =
  {import_kind; import_name; import_as=None; related_by}

let interface_methods intr : ident list =
  let p = function Intr_mdecl m -> Some m.meth_name.node | _ -> None in
  filtermap p intr.intr_elts

let interface_meth_decls intr : meth_decl list =
  filtermap (function Intr_mdecl m -> Some m | _ -> None) intr.intr_elts

let module_methods mdl : ident list =
  filtermap (function
      | Mdl_mdef (Method (m, _)) -> Some m.meth_name.node
      | _ -> None
    ) mdl.mdl_elts

let interface_imports intr : import_directive list =
  let f = function Intr_import import -> Some import | _ -> None in
  filtermap f intr.intr_elts

let module_imports mdl : import_directive list =
  let f = function Mdl_import import -> Some import | _ -> None in
  filtermap f mdl.mdl_elts

let module_private_invariant mdl : named_formula option =
  let get_priv = function
    | Mdl_formula nf when is_private_inv nf -> Some nf
    | _ -> None in
  first_opt get_priv mdl.mdl_elts

let interface_public_invariant intr : named_formula option =
  let get_pub = function
    | Intr_formula nf when is_public_inv nf -> Some nf
    | _ -> None in
  first_opt get_pub intr.intr_elts

let bimodule_coupling bimdl : named_rformula option =
  let get_coupling = function
    | Bimdl_formula nf when is_coupling nf -> Some nf
    | _ -> None in
  first_opt get_coupling bimdl.bimdl_elts

let find_unary_interface penv intr_name =
  match M.find intr_name penv with
  | Unary_interface intr -> intr
  | _ | exception _ -> failwith ("Unknown interface: " ^ id_name intr_name)

let find_unary_module penv mdl_name =
  match M.find mdl_name penv with
  | Unary_module mdl -> mdl
  | _ | exception _ -> failwith ("Unknown module: " ^ id_name mdl_name)

let find_relation_module penv bimdl_name =
  match M.find bimdl_name penv with
  | Relation_module rmdl -> rmdl
  | _ | exception _ -> failwith ("Unknown bimodule: " ^ id_name bimdl_name)


(* -------------------------------------------------------------------------- *)
(* Compute module dependencies                                                *)
(* -------------------------------------------------------------------------- *)

module Deps : sig
  (* TODO: This information should be computed only once.  However, we do it
     twice---once during type checking (using dependencies_parsed_program) and
     once more during translation (using dependencies). 

     Plus, this module should probably be defined in astutil.ml *)
  val dependencies : penv -> ident list
  val dependencies_parsed_program : Ast.program -> ident list
  val sort_by_dependencies : Ast.program -> Ast.program
end = struct
  type gph = (ident * ident list) list

  let imports i =
    if i.import_kind <> Ast.Iregular then [] else
    [i.import_name] @ Option.to_list i.related_by

  let interface_imports intr = concat_map imports (interface_imports intr)

  let module_imports mdl =
    mdl.mdl_interface :: concat_map imports (module_imports mdl)

  let bimodule_imports bm =
    let ext = function
      | Bimdl_import i when i.import_kind = Ast.Iregular -> imports i
      | _ -> [] in
    bm.bimdl_left_impl :: bm.bimdl_right_impl :: concat_map ext bm.bimdl_elts

  let build_gph programs : gph =
    let f = function
      | Unary_interface i -> (i.intr_name, interface_imports i)
      | Unary_module m -> (m.mdl_name, module_imports m)
      | Relation_module bm -> (bm.bimdl_name, bimodule_imports bm)
    in map (f % snd) (M.bindings programs)

  let dfs gph visited start =
    let rec walk path node visited =
      if mem node path then failwith "Cyclic imports" else
      if mem node visited then visited else
        let path = node :: path in
        let succ = assoc node gph in
        node :: foldl (walk path) visited succ
    in walk [] visited start

  let dependencies prog =
    let gph = build_gph prog in
    rev (foldl (fun (node,_) visited -> dfs gph node visited) [] gph)

  let dependencies_parsed_program : Ast.program -> ident list =
    let imports (i:Ast.import_directive Ast.node) =
      if i.elt.import_kind <> Ast.Iregular then [] else
      [i.elt.import_name] @ Option.to_list i.elt.related_by in
    let interface_imports (intr: Ast.interface_def Ast.node) =
      concat_map imports (Astutil.interface_imports intr) in
    let module_imports (mdl: Ast.module_def Ast.node) =
      let intr = mdl.elt.mdl_interface in
      intr :: concat_map imports (Astutil.module_imports mdl) in
    let bimodule_imports (bimdl: Ast.bimodule_def Ast.node) =
      let ext = function
        | Ast.Bimdl_import i when i.elt.import_kind = Ast.Iregular -> imports i
        | _ -> [] in
      bimdl.elt.bimdl_left_impl :: bimdl.elt.bimdl_right_impl 
      :: concat_map ext (Astutil.get_elts bimdl.elt.bimdl_elts) in
    let build_gph (programs: Ast.program) : gph =
      let f = function
        | Ast.{elt=Unr_intr i} -> (i.elt.intr_name, interface_imports i)
        | Ast.{elt=Unr_mdl m} -> (m.elt.mdl_name, module_imports m)
        | Ast.{elt=Rel_mdl bm} -> (bm.elt.bimdl_name, bimodule_imports bm) in
      map f programs in
    fun prog -> 
      let gph = build_gph prog in
      rev (foldl (fun (node,_) visited -> dfs gph node visited) [] gph)

  let sort_by_dependencies (p:Ast.program) : Ast.program =
    let pmap = foldr (fun e acc -> match e.Ast.elt with
      | Ast.Unr_intr i -> M.add i.elt.intr_name e acc
      | Ast.Unr_mdl m -> M.add m.elt.mdl_name e acc
      | Ast.Rel_mdl bm -> M.add bm.elt.bimdl_name e acc
      ) M.empty p in
    let deps = dependencies_parsed_program p in
    foldr (fun name acc -> M.find name pmap :: acc) [] deps

end
