open Lib
open Astutil
open Annot
open Annot.Norm
open Typing


let pretrans_debug = ref false


(* -------------------------------------------------------------------------- *)
(* Rename Locals                                                              *)
(* -------------------------------------------------------------------------- *)

(* Rename any local that shadows any global variable *)
module Rename_Locals : sig
  val rename : penv -> penv
end = struct

  let gen, reset =
    let stamp = ref 0 in
    (fun name -> incr stamp; Ast.Id (name ^ string_of_int !stamp)),
    (fun () -> stamp := 0)

  let gen_ident (i: ident t) : ident t =
    match i.node with
    | Id name -> gen name -: i.ty
    | Qualid _ -> failwith "Qualified identifiers not supported"

  let globals penv : ident list =
    let interface_globals intr =
      let ext = function
        | Intr_vdecl (m, name, ty) -> Some name.node
        | Intr_mdecl m -> Some m.meth_name.node
        | Intr_cdecl c -> Some c.class_name
        | Intr_formula nf -> Some nf.formula_name.node
        | Intr_inductive ind -> Some ind.ind_name.node
        | _ -> None in
      filtermap ext intr.intr_elts in
    let module_globals mdl =
      let ext = function
        | Mdl_cdef (Class c) -> Some c.class_name
        | Mdl_mdef (Method (m, _)) -> Some m.meth_name.node
        | Mdl_vdecl (m, name, ty) -> Some name.node
        | Mdl_formula nf -> Some nf.formula_name.node
        | Mdl_inductive ind -> Some ind.ind_name.node
        | _ -> None in
      filtermap ext mdl.mdl_elts in
    let bimodule_globals bimdl =
      let ext = function
        | Bimdl_formula rnf -> Some rnf.biformula_name
        | Bimdl_mdef (Bimethod (bm, _)) -> Some bm.bimeth_name
        | _ -> None in
      filtermap ext bimdl.bimdl_elts in
    let step k m gbls = match m with
      | Unary_interface i -> interface_globals i @ gbls
      | Unary_module m -> module_globals m @ gbls
      | Relation_module bm -> bimodule_globals bm @ gbls in
    nub @@ M.fold step penv []

  type vsubst = ident t M.t

  let lookup (s: vsubst) (x: ident t) : ident t =
    try M.find x.node s with Not_found -> x

  let ( #! ) s x = lookup s x

  let ( #? ) s x = match x with
    | None -> None
    | Some x -> Some (s #! x)

  let add (s: vsubst) (x: ident t) (y: ident t) : vsubst =
    M.add x.node y s

  let subste (s: vsubst) (e: exp t) : exp t =
    let rec subst e = begin match e.node with
      | Econst c -> Econst c
      | Evar x -> Evar (s #! x)
      | Ebinop (op, e1, e2) -> Ebinop (op, subst e1, subst e2)
      | Eunrop (op, e) -> Eunrop (op, subst e)
      | Esingleton e -> Esingleton (subst e)
      | Eimage (g, f) -> Eimage (subst g, f)
      | Esubrgn (g, k) -> Esubrgn (subst g, k)
      | Ecall (m, es) -> Ecall (m, List.map subst es)
      | Einit e -> Einit (subst e)
      end -: e.ty in
    subst e

  let substlb (s: vsubst) (lb: let_bound_value t) : let_bound_value t =
    begin match lb.node with
    | Lloc (x, f) -> Lloc (s #! x, f)
    | Larr (a, e) -> Larr (s #! a, subste s e)
    | Lexp e -> Lexp (subste s e)
    end -: lb.ty

  (* NOTE: Variables bound by let or quantifiers are not substituted. *)
  let rec substf (s: vsubst) (f: formula) : formula =
    match f with
    | Ftrue | Ffalse -> f
    | Fexp e -> Fexp (subste s e)
    | Finit lb -> Finit (substlb s lb)
    | Fnot f -> Fnot (substf s f)
    | Fpointsto (x, f, e) -> Fpointsto (s #! x, f, subste s e)
    | Farray_pointsto(a, i, e) ->
      let i', e' = subste s i, subste s e in
      Farray_pointsto (s #! a, i', e')
    | Fsubseteq (e1, e2) -> Fsubseteq (subste s e1, subste s e2)
    | Fdisjoint (e1, e2) -> Fdisjoint (subste s e1, subste s e2)
    | Fmember (e1, e2) -> Fmember (subste s e1, subste s e2)
    | Flet (x, ({node={value=lb; _} as l; ty}), f) ->
      let l' = {l with value = substlb s lb} in
      Flet (x, l' -: ty, substf s f)
    | Fconn (c, f1, f2) -> Fconn (c, substf s f1, substf s f2)
    | Fquant (q, qbinds, f) -> Fquant (q, substqbs s qbinds, substf s f)
    | Fold (e, lb) -> Fold (subste s e, substlb s lb)
    | Ftype (e, k) -> Ftype (subste s e, k)

  and substqbs (s: vsubst) (qbinds: qbinders) : qbinders =
    let subst ({in_rgn} as qbind) =
      match in_rgn with
      | None -> qbind
      | Some e -> {qbind with in_rgn = Some (subste s e)}
    in map subst qbinds

  let rec substeff (s: vsubst) (eff: effect) : effect =
    match eff with
    | [] -> []
    | {effect_kind; effect_desc = {node = Effvar x} as e} :: rest ->
      let effect_desc = {node = Effvar (s #! x); ty = e.ty} in
      {effect_kind; effect_desc} :: substeff s rest
    | {effect_kind; effect_desc = {node = Effimg (g,f)} as e} :: rest ->
      let effect_desc = {node = Effimg (subste s g,f); ty = e.ty} in
      {effect_kind; effect_desc} :: substeff s rest

  let substac (s: vsubst) (ac: atomic_command) : atomic_command =
    match ac with
    | Skip -> Skip
    | Assign (x, e) -> Assign (s #! x, subste s e)
    | Havoc x -> Havoc (s #! x)
    | New_class (x, k) -> New_class (s #! x, k)
    | New_array (x, k, e) -> New_array (s #! x, k, subste s e)
    | Field_deref (x, y, f) -> Field_deref (s #! x, s #! y, f)
    | Field_update (x, f, e) -> Field_update (s #! x, f, subste s e)
    | Array_access (x, a, i) -> Array_access (s #! x, s #! a, subste s i)
    | Array_update (a, i, e) -> Array_update (s #! a, subste s i, subste s e)
    | Call (x, m, es) -> Call (s #? x, m, List.map ((#!) s) es)

  let substc (gbls: ident list) (s: vsubst) (c: command) : command =
    let rec subst s = function
      | Acommand ac -> Acommand (substac s ac)
      | Vardecl (x, m, ty, c) when List.mem x.node gbls ->
        let x' = gen_ident x in
        if !pretrans_debug then begin
          let x_name = string_of_ident x.node in
          let x'_name = string_of_ident x'.node in
          Printf.fprintf stderr "Renaming %s to %s\n" x_name x'_name
        end;
        Vardecl (x', m, ty, subst (add s x x') c)
      | Vardecl (x, m, ty, c) -> Vardecl (x, m, ty, subst s c)
      | Seq (c1, c2) -> Seq (subst s c1, subst s c2)
      | If (e, c1, c2) -> If (subste s e, subst s c1, subst s c2)
      | While (e, {winvariants; wframe; wvariant}, c) ->
        let winvariants = map (substf s) winvariants in
        let wframe = substeff s wframe in
        let wvariant = Option.map (subste s) wvariant in
        While (subste s e, {winvariants; wframe; wvariant}, subst s c)
      | Assume f -> Assume (substf s f)
      | Assert f -> Assert (substf s f) in
    subst s c

  let rename_meth_def gbls mdef : meth_def =
    let Method (mdecl, com) = mdef in
    match com with
    | None -> Method (mdecl, None)
    | Some c -> reset (); Method (mdecl, Some (substc gbls M.empty c))

  let rename_in_module gbls mdl : module_def =
    let mdl_elts = List.fold_right (fun elt rest ->
        match elt with
        | Mdl_mdef mdef -> Mdl_mdef (rename_meth_def gbls mdef) :: rest
        | _ -> elt :: rest
      ) mdl.mdl_elts [] in
    { mdl with mdl_elts }

  let rename penv =
    let gbls = globals penv in
    let process name m env = match m with
      | Unary_module m ->
        let m' = rename_in_module gbls m in
        M.add name (Unary_module m') env
      | _ -> M.add name m env in
    M.fold process penv M.empty
end
