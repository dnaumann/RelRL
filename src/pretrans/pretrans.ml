(** pretrans.ml -- transformations on annotated ASTs *)

open Lib
open Astutil
open Annot
open Annot.Norm
open Typing

let pretrans_debug = ref false
let simplify_effects = ref true

(* -------------------------------------------------------------------------- *)
(* Expand specs to include invariants, and in modules, the interface spec     *)
(* -------------------------------------------------------------------------- *)

module Expand_method_spec : sig
  val expand : penv -> penv
end = struct

  let conjoin_inv mdecl inv =
    let inv_holds nf = Fexp (Ecall (nf.formula_name, []) -: Tprop) in
    let prepost_inv = [Precond (inv_holds inv); Postcond (inv_holds inv)] in
    {mdecl with meth_spec = mdecl.meth_spec @ prepost_inv}

  let conjoin_coupling bimdecl coupling =
    let name = coupling.biformula_name in
    let it_holds = Rprimitive {name; left_args=[]; right_args=[]} in
    let prepost_it = [Biprecond it_holds; Bipostcond it_holds] in
    {bimdecl with bimeth_spec = bimdecl.bimeth_spec @ prepost_it}

  let add_publicinv_to_interface_specs intr : interface_def =
    let walk inv elt acc = match elt with
      | Intr_mdecl mdecl -> Intr_mdecl (conjoin_inv mdecl inv) :: acc
      | _ -> elt :: acc in
    match interface_public_invariant intr with
    | None -> intr
    | Some pub -> {intr with intr_elts = foldr (walk pub) [] intr.intr_elts}

  let find_interface_methods penv intr_name =
    let intr = find_unary_interface penv intr_name in
    let accum_meths elt acc = match elt with
      | Intr_mdecl mdecl -> mdecl.meth_name.node :: acc
      | _ -> acc in
    foldr accum_meths [] intr.intr_elts

  let add_privateinv_to_module_specs penv mdl : module_def =
    let walk interface_meths inv elt acc = match elt with
      | Mdl_mdef (Method (mdecl, com)) ->
        if mem mdecl.meth_name.node interface_meths
        then Mdl_mdef (Method (conjoin_inv mdecl inv, com)) :: acc
        else elt :: acc
      | _ -> elt :: acc in
    let interface_meths = find_interface_methods penv mdl.mdl_interface in
    match module_private_invariant mdl with
    | None -> mdl
    | Some priv ->
      let mdl_elts = foldr (walk interface_meths priv) [] mdl.mdl_elts in
      {mdl with mdl_elts}

  let add_coupling_to_bimodule_specs penv bimdl : bimodule_def =
    let walk interface_meths inv elt acc = match elt with
      | Bimdl_mdef (Bimethod (bimdecl, bicom)) ->
        if mem bimdecl.bimeth_name interface_meths
        then Bimdl_mdef (Bimethod (conjoin_coupling bimdecl inv, bicom)) :: acc
        else elt :: acc
      | _ -> elt :: acc in
    let left_mdl = find_unary_module penv bimdl.bimdl_left_impl in
    let interface_methods = find_interface_methods penv left_mdl.mdl_interface in
    match bimodule_coupling bimdl with
    | None -> bimdl
    | Some priv ->
      let elts = foldr (walk interface_methods priv) [] bimdl.bimdl_elts in
      {bimdl with bimdl_elts = elts}

  let find_interface_spec penv intr meth : spec option =
    let intr_str = string_of_ident intr in
    match M.find intr penv with
    | Unary_interface {intr_name; intr_elts} ->
      let intr_meth_spec = List.filter_map (function
          | Intr_mdecl mdecl when mdecl.meth_name.node = meth ->
            Some mdecl.meth_spec
          | _ -> None
        ) intr_elts in
      begin match intr_meth_spec with
        | [] -> None
        | ss -> Some (last ss)
      end
    | _ | exception Not_found ->
      failwith @@ "Unknown interface: " ^ intr_str

  let expand_meth_def_in_module penv intr mdef : meth_def =
    let Method (mdecl, com) = mdef in
    let intr_spec = find_interface_spec penv intr mdecl.meth_name.node in
    let meth_spec = match intr_spec with
      | Some s -> s @ mdecl.meth_spec
      | None -> mdecl.meth_spec in
    Method ({mdecl with meth_spec}, com)

  let expand_module penv mdl : module_def =
    let intr = mdl.mdl_interface in
    let elts = List.map (function
        | Mdl_mdef mdef ->
          let mdef' = expand_meth_def_in_module penv intr mdef in
          Mdl_mdef mdef'
        | e -> e
      ) mdl.mdl_elts in
    {mdl with mdl_elts = elts}

  let add_pubinv programs = M.map (function
      | Unary_interface intr ->
        Unary_interface (add_publicinv_to_interface_specs intr)
      | other -> other
    ) programs

  let add_privinv programs = M.map (function
      | Unary_module mdl ->
        Unary_module (add_privateinv_to_module_specs programs mdl)
      | other -> other
    ) programs

  let add_coupling programs = M.map (function
      | Relation_module bimdl ->
        Relation_module (add_coupling_to_bimodule_specs programs bimdl)
      | other -> other
    ) programs

  let expand programs =
    (* First add invariants to specs in interfaces, modules, and bimodules *)
    let programs = add_coupling (add_privinv (add_pubinv programs)) in
    (* Then expand specs in modules to include relevant specs in interfaces *)
    M.map (function
        | Unary_module mdl -> Unary_module (expand_module programs mdl)
        | other -> other
      ) programs
end


(* -------------------------------------------------------------------------- *)
(* Normalize effects                                                          *)
(* -------------------------------------------------------------------------- *)

module Normalize_effects : sig
  val normalize : penv -> penv
end = struct

  let normalize_spec spec =
    let obtaineff = function Effects e -> Some e | _ -> None in
    let wo_effect = List.filter (Option.is_none % obtaineff) spec in
    let effects = concat_filter_map obtaineff spec in
    wo_effect @ [T.Effects (normalize effects)]

  let rec normalize_command com =
    match com with
    | Assume f -> Assume f
    | Assert f -> Assert f
    | Acommand ac -> Acommand ac
    | Vardecl (x, m, t, c) -> Vardecl (x, m, t, normalize_command c)
    | Seq (c1, c2) -> Seq (normalize_command c1, normalize_command c2)
    | If (e, c1, c2) -> If (e, normalize_command c1, normalize_command c2)
    | While (e, {winvariants; wframe; wvariant}, c) ->
      let wframe = normalize wframe in
      While (e, {winvariants; wframe; wvariant}, normalize_command c)

  let normalize_command_opt = function
    | None -> None
    | Some c -> Some (normalize_command c)

  let rec normalize_bicommand bicom =
    match bicom with
    | Bihavoc_right (x, rf) -> Bihavoc_right (x, rf)
    | Bisplit (c, c') -> Bisplit (normalize_command c, normalize_command c')
    | Bisync ac -> Bisync ac
    | Bivardecl (x, x', cc) -> Bivardecl (x, x', normalize_bicommand cc)
    | Biseq (cc, cc') -> Biseq (normalize_bicommand cc, normalize_bicommand cc')
    | Biif (e, e', cc, dd) ->
      Biif (e, e', normalize_bicommand cc, normalize_bicommand dd)
    | Biif4 (e, e', branches) ->
      Biif4 (e, e', map_fourwayif normalize_bicommand branches)
    | Biwhile (e, e', ag, {biwinvariants; biwframe; biwvariant}, cc) ->
      let biwframe = map_pair normalize biwframe in
      let cc = normalize_bicommand cc in
      Biwhile (e, e', ag, {biwinvariants; biwframe; biwvariant}, cc)
    | Biassume rf -> Biassume rf
    | Biassert rf -> Biassert rf
    | Biupdate (x, x') -> Biupdate (x, x')

  let normalize_bicommand_opt = function
    | None -> None
    | Some cc -> Some (normalize_bicommand cc)

  let normalize_meth_decl mdecl =
    { mdecl with meth_spec = normalize_spec mdecl.meth_spec }

  let normalize_meth_def mdef =
    let Method (mdecl, com) = mdef in
    Method (normalize_meth_decl mdecl, normalize_command_opt com)

  let normalize_bispec bispec =
    let obtaineff = function Bieffects (l,r) -> Some (l,r) | _ -> None in
    let wo_effect = List.filter (Option.is_none % obtaineff) bispec in
    let effects = unzip (List.filter_map obtaineff bispec) in
    let el,er = map_pair (normalize % List.flatten) effects in
    wo_effect @ [Bieffects(el,er)]

  let normalize_bimeth_decl bimdecl =
    { bimdecl with bimeth_spec = normalize_bispec bimdecl.bimeth_spec }

  let normalize_bimeth_def bimeth =
    let Bimethod (bimdecl, com) = bimeth in
    Bimethod (normalize_bimeth_decl bimdecl, normalize_bicommand_opt com)

  let normalize_interface intr : interface_def =
    let elts = List.fold_right (fun elt rest ->
        match elt with
        | Intr_boundary bnd -> Intr_boundary (normalize_boundary bnd) :: rest
        | Intr_mdecl mdecl -> Intr_mdecl (normalize_meth_decl mdecl) :: rest
        | _ -> elt :: rest
      ) intr.intr_elts [] in
    { intr with intr_elts = elts }

  let normalize_module mdl : module_def =
    let elts = List.fold_right (fun elt rest ->
        match elt with
        | Mdl_mdef mdef -> Mdl_mdef (normalize_meth_def mdef) :: rest
        | _ -> elt :: rest
      ) mdl.mdl_elts [] in
    { mdl with mdl_elts = elts }

  let normalize_bimodule bimdl : bimodule_def =
    let elts = List.fold_right (fun elt rest ->
        match elt with
        | Bimdl_mdef mdef -> Bimdl_mdef (normalize_bimeth_def mdef) :: rest
        | _ -> elt :: rest
      ) bimdl.bimdl_elts [] in
    { bimdl with bimdl_elts = elts }

  let normalize penv = M.fold (fun k v progs ->
      match v with
      | Unary_module m ->
        let m' = normalize_module m in
        M.add k (Unary_module m') progs
      | Unary_interface i ->
        let i' = normalize_interface i in
        M.add k (Unary_interface i') progs
      | Relation_module b ->
        let b' = normalize_bimodule b in
        M.add k (Relation_module b') progs
    ) penv M.empty

end


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


(* -------------------------------------------------------------------------- *)
(* Boundary Monotonicity spec                                                 *)
(* -------------------------------------------------------------------------- *)

module Boundary_mono_spec : sig
  val extend_specs : penv -> penv
end = struct

  type bnd_snapshot = (exp t * ident t) list

  let bnd_snap_name, reset =
    let id name = Ast.Id name in
    let stamp = ref 0 in
    (fun r -> incr stamp; id ("bsnap_" ^ r ^ string_of_int !stamp)),
    (fun () -> stamp := 0)

  let bnd_snap (bnd: boundary_decl) : bnd_snapshot =
    let rec nameof_rgn e = match e.node with
      | Evar {node=Id name; _} -> name
      | Esingleton {node=Evar {node=Id name; _}; _} -> name
      | _ -> "r" in
    let snapshot snap e name =
      if List.mem_assoc e snap then snap
      else (e, name) :: snap in
    let rec walk snap bnd = match bnd with
      | [] -> snap
      | e :: es ->
        match e.node with
        | Effvar x -> walk snap es
        | Effimg (g, f) ->
          let name = bnd_snap_name (nameof_rgn (Eimage(g,f) -: Trgn)) in
          walk (snapshot snap g (name -: g.ty)) es in
    walk [] bnd

  let bnd_mon (bsnap: bnd_snapshot) : formula option =
    let mk_conj f1 f2 = Fconn (Conj, f1, f2) in
    let mk_increases snap_var curr_rgn =
      let snap_exp = Evar snap_var -: snap_var.ty in
      Fsubseteq (snap_exp, curr_rgn) in
    let old e =
      {is_old = true; is_init = false; value = Lexp e -: e.ty} -: e.ty in
    let rec walk frm = function
      | [] -> frm
      | (e, id) :: rest ->
        Flet (id, old e, walk (mk_conj frm (mk_increases id e)) rest) in
    match bsnap with
    | [] -> None
    | (e, id) :: rest -> Some (Flet (id, old e, walk (mk_increases id e) rest))

  type mdl_bnd_post = formula option M.t

  let mdl_bnd_post_of_penv penv : mdl_bnd_post =
    let step name _ postmap =
      let bnd = Boundary_info.boundary name in
      let mono_frm = bnd_mon (bnd_snap bnd) in
      M.add name mono_frm postmap in
    M.fold step penv M.empty

  let extend_spec bmon curr_mdl spec : spec =
    match M.find curr_mdl bmon with
    | None -> spec
    | Some frm -> Postcond frm :: spec

  let extend_bispec bmon curr_mdl bispec : bispec =
    match M.find curr_mdl bmon with
    | None -> bispec
    | Some frm -> Bipostcond (Rboth frm) :: bispec

  let extend_meth_decl bmon curr_mdl mdecl =
    {mdecl with meth_spec = extend_spec bmon curr_mdl mdecl.meth_spec}

  let extend_meth_def bmon curr_mdl mdef =
    let Method (mdecl, com) = mdef in
    Method (extend_meth_decl bmon curr_mdl mdecl, com)

  let extend_bimeth_decl bmon curr_mdl bimdecl =
    let bimeth_spec = extend_bispec bmon curr_mdl bimdecl.bimeth_spec in
    {bimdecl with bimeth_spec}

  let extend_bimeth bmon curr_mdl bimeth =
    let Bimethod (bimdecl, bicom) = bimeth in
    let bimdecl' = extend_bimeth_decl bmon curr_mdl bimdecl in
    Bimethod (bimdecl', bicom)

  let extend_interface bmon intr =
    let curr_mdl = intr.intr_name in
    let step elt elts = match elt with
      | Intr_mdecl mdecl ->
        let mdecl' = extend_meth_decl bmon curr_mdl mdecl in
        Intr_mdecl mdecl' :: elts
      | _ -> elt :: elts in
    {intr with intr_elts = List.fold_right step intr.intr_elts []}

  let extend_module bmon mdl =
    let curr_mdl = mdl.mdl_name in
    let step elt elts = match elt with
      | Mdl_mdef mdef ->
        let mdef' = extend_meth_def bmon curr_mdl mdef in
        Mdl_mdef mdef' :: elts
      | _ -> elt :: elts in
    {mdl with mdl_elts = List.fold_right step mdl.mdl_elts []}

  let extend_bimodule bmon bimdl =
    let curr_mdl = bimdl.bimdl_name in
    let step elt elts = match elt with
      | Bimdl_mdef bimdef ->
        let bimdef' = extend_bimeth bmon curr_mdl bimdef in
        Bimdl_mdef bimdef' :: elts
      | _ -> elt :: elts in
    {bimdl with bimdl_elts = List.fold_right step bimdl.bimdl_elts []}

  let extend_specs penv =
    let bmon = mdl_bnd_post_of_penv penv in
    let step name mdl prog = match mdl with
      | Unary_interface i ->
        reset ();
        let i' = Unary_interface (extend_interface bmon i) in
        M.add name i' prog
      | Unary_module m ->
        reset ();
        let m' = Unary_module (extend_module bmon m) in
        M.add name m' prog
      | Relation_module b ->
        reset ();
        let b' = Relation_module (extend_bimodule bmon b) in
        M.add name b' prog in
    M.fold step penv M.empty
end


(* -------------------------------------------------------------------------- *)
(* Perform simplifications on normalized effects                              *)
(* -------------------------------------------------------------------------- *)

module Simplify_effects : sig
  val simplify : Ctbl.t * penv -> penv
end = struct

  let emptyrgn = {node = Econst {node = Eemptyset; ty = Trgn}; ty = Trgn}

  let is_emptyrgn = function
    | {node = Econst {node = Eemptyset}} -> true
    | _ -> false

  let mk_union (e1, e2) : exp t =
    if is_emptyrgn e1 then e2 else
    if is_emptyrgn e2 then e1 else Ebinop (Union, e1, e2) -: Trgn

  let mk_inter (e1, e2) : exp t =
    if is_emptyrgn e1 || is_emptyrgn e2 then emptyrgn
    else Ebinop (Inter, e1, e2) -: Trgn

  let mk_diff (e1, e2) : exp t =
    if is_emptyrgn e1 then emptyrgn else
    if is_emptyrgn e2 then e1 else Ebinop (Diff, e1, e2) -: Trgn

  let rec simplify_region_exp (ctbl: Ctbl.t) (g: exp t) (f: ident t) =
    match g.node with
    | Esingleton x when is_class_ty x.ty ->
      let k = match x.ty with Tclass k -> k | _ -> assert false in
      let flds = map (uncurry (-:)) @@ Ctbl.fields ctbl ~classname:k in
      if mem f flds then g else emptyrgn
    | Ebinop (Union, g1, g2) ->
      let g1' = simplify_region_exp ctbl g1 f in
      let g2' = simplify_region_exp ctbl g2 f in
      mk_union (g1', g2')
    | Ebinop (Inter, g1, g2) ->
      let g1' = simplify_region_exp ctbl g1 f in
      let g2' = simplify_region_exp ctbl g2 f in
      mk_inter (g1', g2')
    | Ebinop (Diff, g1, g2) ->
      let g1' = simplify_region_exp ctbl g1 f in
      let g2' = simplify_region_exp ctbl g2 f in
      mk_diff (g1', g2')
    | _ -> g

  let rec simplify_effect_elt (ctbl: Ctbl.t) (eff: effect_elt) : effect =
    match eff.effect_desc with
    | {node = Effimg (g, f); ty} ->
      let g' = simplify_region_exp ctbl g f in
      let effect_desc = {node = Effimg (g', f); ty} in
      if is_emptyrgn g' then [] else [{eff with effect_desc}]
    | _ -> [eff]

  let simplify_effect ctbl (eff: effect) : effect =
    concat_map (simplify_effect_elt ctbl) eff

  let simplify_spec ctbl (spec: spec) : spec =
    let wo_effs = filter (function Effects _ -> false | _ -> true) spec in
    let eff = simplify_effect ctbl (spec_effects spec) in
    wo_effs @ [Effects eff]

  let rec simplify_command ctbl (c: command) =
    match c with
    | Acommand ac -> Acommand ac
    | Vardecl (x, m, ty, c) ->
      Vardecl (x, m, ty, simplify_command ctbl c)
    | Seq (c1, c2) ->
      Seq (simplify_command ctbl c1, simplify_command ctbl c2)
    | If (e, c1, c2) ->
      If (e, simplify_command ctbl c1, simplify_command ctbl c2)
    | While (e, wspec, c) ->
      let wspec = {wspec with wframe = simplify_effect ctbl wspec.wframe} in
      While (e, wspec, simplify_command ctbl c)
    | Assume f -> Assume f
    | Assert f -> Assert f

  let simplify_meth_decl ctbl mdecl =
    {mdecl with meth_spec = simplify_spec ctbl mdecl.meth_spec}

  let simplify_meth_def ctbl = function
    | Method (mdecl, com) ->
      let com' = Option.map (simplify_command ctbl) com in
      Method (simplify_meth_decl ctbl mdecl, com')

  let simplify_interface ctbl intr : interface_def =
    let simplify = function
      | Intr_boundary bnd ->
        let f = bnd_of_eff % simplify_effect ctbl % eff_of_bnd in
        Intr_boundary (f bnd)
      | Intr_mdecl m -> Intr_mdecl (simplify_meth_decl ctbl m)
      | e -> e in
    {intr with intr_elts = map simplify intr.intr_elts}

  let simplify_module ctbl mdl : module_def =
    let simplify = function
      | Mdl_mdef m -> Mdl_mdef (simplify_meth_def ctbl m)
      | e -> e in
    {mdl with mdl_elts = map simplify mdl.mdl_elts}

  let rec simplify_bicommand ctbl = function
    | Bihavoc_right (x, rf) -> Bihavoc_right (x, rf)
    | Bisplit (c, c') ->
      Bisplit (simplify_command ctbl c, simplify_command ctbl c')
    | Bisync ac -> Bisync ac
    | Bivardecl (x, x', cc) -> Bivardecl (x, x', simplify_bicommand ctbl cc)
    | Biseq (cc, cc') ->
      Biseq (simplify_bicommand ctbl cc, simplify_bicommand ctbl cc')
    | Biif (e, e', cc, cc') ->
      Biif (e, e', simplify_bicommand ctbl cc, simplify_bicommand ctbl cc')
    | Biif4 (e, e', branches) ->
      Biif4 (e, e', map_fourwayif (simplify_bicommand ctbl) branches)
    | Biwhile (e, e', ag, biwspec, cc) ->
      let biwframe = map_pair (simplify_effect ctbl) biwspec.biwframe in
      let biwspec = {biwspec with biwframe} in
      Biwhile (e, e', ag, biwspec, simplify_bicommand ctbl cc)
    | Biassume rf -> Biassume rf
    | Biassert rf -> Biassert rf
    | Biupdate (x, x') -> Biupdate (x, x')

  let simplify_bispec ctbl (bispec: bispec) : bispec =
    let wo_effs = filter (function Bieffects _ -> false | _ -> true) bispec in
    let ext = function Bieffects (e,e') -> Some (e,e') | _ -> None in
    let leff, reff = List.split (filtermap ext bispec) in
    let leff, reff = map_pair (simplify_effect ctbl) (flat leff, flat reff) in
    let eff = Bieffects (leff, reff) in
    wo_effs @ [eff]

  let simplify_bimeth_decl ctbl bimdecl =
    {bimdecl with bimeth_spec = simplify_bispec ctbl bimdecl.bimeth_spec}

  let simplify_bimeth_def ctbl bimeth =
    let Bimethod (bimdecl, com) = bimeth in
    let com' = Option.map (simplify_bicommand ctbl) com in
    Bimethod (simplify_bimeth_decl ctbl bimdecl, com')

  let simplify_bimodule ctbl bimdl : bimodule_def =
    let simplify = function
      | Bimdl_mdef mdef ->
        let mdef' = simplify_bimeth_def ctbl mdef in
        Bimdl_mdef mdef'
      | e -> e in
    {bimdl with bimdl_elts = map simplify bimdl.bimdl_elts}

  let simplify (ctbl, penv) =
    if not !simplify_effects then penv else
      let simp = function
        | Unary_interface i -> Unary_interface (simplify_interface ctbl i)
        | Unary_module m -> Unary_module (simplify_module ctbl m)
        | Relation_module b -> Relation_module (simplify_bimodule ctbl b) in
      M.map simp penv

end


(* -------------------------------------------------------------------------- *)
(* Refine write effects of implementations                                    *)
(* -------------------------------------------------------------------------- *)

module Refine_writes : sig
  val refine : Ctbl.t * penv -> penv
end = struct

  (* This pass is required to handle an issue with Why3's writes clause.

     WhyRel translates source programs to Why3 programs that operate on an
     encoding of program states.  States are represented using Why3 records
     containing mutable fields.  Programs modify these fields.

     Why3 expects the writes clause to be exact: if a field f is not written to
     by an implementation, it may not show up in the writes clause.

     This pass removes unnecessary writes in specs associated with methods and
     bimethods.  For a method m with body C:
     - (wr x) is unnecessary if x is not written to in C.
     - (wr G`f) is unnecessary if there isn't a write to any object's f field
       in C.  The region G does not matter.

     This pass assumes:
     A1. The any datagroup has been expanded (see Resolve_datagroups).
     A2. All effects have been normalized (see Normalize_effects).
  *)

  (* A write-target is either a variable or a field name. *)
  type wr_target =
    | Wt_var of ident t
    | Wt_field of ident t

  module WtS = (val mk_set compare : Set.S with type elt = wr_target)

  type ctxt = {ctbl: Ctbl.t; meth_wrs: WtS.t M.t}

  let pp_wts outf wts =
    let to_string = function
      | Wt_var x -> pp_as_string Pretty.pp_ident x.node
      | Wt_field f -> pp_as_string Pretty.pp_ident f.node in
    let elts = String.concat ", " % map to_string @@ WtS.elements wts in
    Format.fprintf outf "{ %s }" elts

  (* refine_effect eff s = 
     (rds eff) union {wr x in eff | x in s} union {wr G`f in eff | f in s} *)
  let refine_effect (eff: effect) (s: WtS.t) : effect =
    let keep e = is_read e || match e.effect_desc.node with
      | Effimg (_,f) -> WtS.mem (Wt_field f) s
      | Effvar x -> WtS.mem (Wt_var x) s in
    assert (is_normalized eff);
    filter keep eff

  let refine_spec (spec: spec) (s: WtS.t) : spec =
    let spec_wo_effs = filter (function Effects _ -> false | _ -> true) spec in
    let spec_effs = spec_effects spec in
    let spec_effs_refined = refine_effect spec_effs s in
    spec_wo_effs @ [Effects (spec_effs_refined)]

  let write_targets_of_effect (eff: effect) : WtS.t =
    let rec aux s = function
      | [] -> s
      | {effect_kind = Write; effect_desc = {node = Effvar x}} :: eff ->
        aux (WtS.union (WtS.singleton (Wt_var x)) s) eff
      | {effect_kind = Write; effect_desc = {node = Effimg (g,f)}} :: eff ->
        aux (WtS.union (WtS.singleton (Wt_field f)) s) eff
      | _ :: eff -> aux s eff in
    aux WtS.empty eff

  let write_targets_of_spec = write_targets_of_effect % spec_effects

  let rec write_targets_of_exp (ctxt: ctxt) (e: exp t) : WtS.t =
    match e.node with
    | Econst _ | Evar _ | Esingleton _ | Eimage _ | Esubrgn _ -> WtS.empty
    | Ebinop (_, e1, e2) ->
      WtS.union (write_targets_of_exp ctxt e1) (write_targets_of_exp ctxt e2)
    | Einit e | Eunrop (_, e) -> write_targets_of_exp ctxt e
    | Ecall (m, args) ->
      let mwrs = try M.find m.node ctxt.meth_wrs with
        | Not_found -> WtS.empty in
      let args_wrs = List.map (write_targets_of_exp ctxt) args in
      let args_wrs = foldr WtS.union WtS.empty args_wrs in
      WtS.union mwrs args_wrs

  let alloc_wt = Wt_var (Ast.Id "alloc" -: Trgn)

  let write_targets (ctxt: ctxt) (com: command) : WtS.t =
    let rec of_atomic_command = function
      | Field_deref _ -> WtS.empty
      | Array_access (x, _, e) | Assign (x, e) ->
        WtS.add (Wt_var x) (write_targets_of_exp ctxt e)
      | Havoc x -> WtS.singleton (Wt_var x)
      | New_class (x, k) | New_array (x, k, _) ->
        let flds = Ctbl.fields ctxt.ctbl ~classname:k in
        let flds = map (fun e -> fst e -: snd e) flds in
        let fld_wrs = WtS.of_list (map (fun f -> Wt_field f) flds) in
        WtS.add alloc_wt (WtS.add (Wt_var x) fld_wrs)
      | Field_update (x, f, e) ->
        WtS.add (Wt_field f) (write_targets_of_exp ctxt e)
      | Array_update (a, i, e) ->
        (* An array update does not modify the length field *)
        assert (is_class_ty a.ty);
        let classname = match a.ty with
          | Tclass cname -> cname
          | _ -> assert false in
        assert (Ctbl.is_array_like_class ctxt.ctbl ~classname);
        let slotsf = Ctbl.array_like_slots_field ctxt.ctbl ~classname in
        let slotsf = (fun e -> fst e -: snd e) (Option.get slotsf) in
        let iwrs, ewrs = map_pair (write_targets_of_exp ctxt) (i, e) in
        WtS.add (Wt_field slotsf) (WtS.union iwrs ewrs)
      | Call (xopt, meth, args) ->
        let mwrs = try M.find meth.node ctxt.meth_wrs with
          | Not_found -> WtS.empty in
        let xwr = match xopt with
          | None -> WtS.empty
          | Some x -> WtS.singleton (Wt_var x) in
        WtS.union mwrs xwr
      | Skip -> WtS.empty in
    let rec of_command = function
      | Acommand ac -> of_atomic_command ac
      | Vardecl (_, _, _, c) -> of_command c
      | Seq (c1, c2) -> WtS.union (of_command c1) (of_command c2)
      | If (e, c1, c2) -> WtS.union (of_command c1) (of_command c2)
      | While (e, wspec, c) -> of_command c
      | Assume _ | Assert _ -> WtS.empty
    in of_command com

  let rec refine_command (ctxt: ctxt) (com: command) : command =
    match com with
    | Acommand ac -> Acommand ac
    | Vardecl (x, m, ty, c) -> Vardecl (x, m, ty, refine_command ctxt c)
    | Seq (c1, c2) -> Seq (refine_command ctxt c1, refine_command ctxt c2)
    | If (e, c1, c2) -> If (e, refine_command ctxt c1, refine_command ctxt c2)
    | While (e, wspec, c) ->
      let wrs = write_targets ctxt c in
      let wspec = {wspec with wframe = refine_effect wspec.wframe wrs} in
      While (e, wspec, refine_command ctxt c)
    | Assume f -> Assume f
    | Assert f -> Assert f

  let dest_meth_def (m: meth_def) : meth_decl * command option =
    match m with Method (mdecl, c) -> mdecl, c

  let refine_meth_def (ctxt: ctxt) (m: meth_def) : ctxt * meth_def =
    let mdecl, com = dest_meth_def m in
    let spec'd_wts = write_targets_of_spec mdecl.meth_spec in
    (* NOTE: WhyRel doesn't support recursive calls at the moment, but if it
       did, the context should include the actual write-targets instead of the
       specified ones.  The actual write-targets of a recursive method can be
       found by computing write_targets of a copy of the method's body without
       recursive calls. *)
    let meth_wrs = M.add mdecl.meth_name.node spec'd_wts ctxt.meth_wrs in
    let ctxt = {ctxt with meth_wrs} in 
    match com with
    | None ->
      ctxt, Method (mdecl, None)
    | Some com ->
      let actual_wts = write_targets ctxt com in
      let meth_spec = refine_spec mdecl.meth_spec actual_wts in
      let mdecl = {mdecl with meth_spec} in
      let meth_wrs = M.add mdecl.meth_name.node actual_wts ctxt.meth_wrs in
      let ctxt = {ctxt with meth_wrs} in
      ctxt, Method (mdecl, Some (refine_command ctxt com))

  let refine_interface (ctxt: ctxt) (i: interface_def) : ctxt * interface_def =
    let ctxt, intr_elts = foldr (fun elt (ctxt,elts) ->
        match elt with
        | Intr_mdecl m ->
          let ctxt, Method (m', _) = refine_meth_def ctxt (Method (m, None)) in
          (ctxt, Intr_mdecl m' :: elts)
        | _ -> (ctxt, elt :: elts)
      ) (ctxt,[]) i.intr_elts in
    ctxt, {i with intr_elts}

  let refine_module (ctxt: ctxt) (m: module_def) : ctxt * module_def =
    let ctxt, mdl_elts = foldr (fun elt (ctxt, elts) ->
        match elt with
        | Mdl_mdef m ->
          let ctxt, m' = refine_meth_def ctxt m in
          ctxt, Mdl_mdef m' :: elts
        | _ -> ctxt, elt :: elts
      ) (ctxt, []) m.mdl_elts in
    ctxt, {m with mdl_elts}

  type bi_ctxt = { lft: ctxt; rgt: ctxt; bimeth_wrs: (WtS.t * WtS.t) M.t }

  let rec write_targets_of_bicommand bi_ctxt bicom : (WtS.t * WtS.t) =
    match bicom with
    | Bihavoc_right (x, rf) ->
      WtS.empty, write_targets bi_ctxt.rgt (projr bicom)
    | Bisplit (c, c') ->
      write_targets bi_ctxt.lft c, write_targets bi_ctxt.rgt c'
    | Bisync (Call (xopt, bimeth, args)) ->
      (* Treated as a call to a bimethod *)
      let lwrs, rwrs = try M.find bimeth.node bi_ctxt.bimeth_wrs with
        | Not_found -> WtS.empty, WtS.empty in
      let xwr = match xopt with
        | None -> WtS.empty | Some x -> WtS.singleton (Wt_var x) in
      WtS.union xwr lwrs, WtS.union xwr rwrs
    | Bisync ac ->
      let lwrs = write_targets bi_ctxt.lft (Acommand ac) in
      let rwrs = write_targets bi_ctxt.rgt (Acommand ac) in
      lwrs, rwrs
    | Bivardecl (_, _, cc) -> write_targets_of_bicommand bi_ctxt cc
    | Biseq (cc, cc') ->
      let lwrs, rwrs = write_targets_of_bicommand bi_ctxt cc in
      let lwrs', rwrs' = write_targets_of_bicommand bi_ctxt cc' in
      WtS.union lwrs lwrs', WtS.union rwrs rwrs'
    | Biif (_, _, cc, cc') ->
      let lwrs, rwrs = write_targets_of_bicommand bi_ctxt cc in
      let lwrs', rwrs' = write_targets_of_bicommand bi_ctxt cc' in
      WtS.union lwrs lwrs', WtS.union rwrs rwrs'
    | Biif4 (_, _, {then_then; then_else; else_then; else_else}) ->
      let lwrs1, rwrs1 = write_targets_of_bicommand bi_ctxt then_then in
      let lwrs2, rwrs2 = write_targets_of_bicommand bi_ctxt then_else in
      let lwrs3, rwrs3 = write_targets_of_bicommand bi_ctxt else_then in
      let lwrs4, rwrs4 = write_targets_of_bicommand bi_ctxt else_else in
      foldr1 WtS.union [lwrs1; lwrs2; lwrs3; lwrs4],
      foldr1 WtS.union [rwrs1; rwrs2; rwrs3; rwrs4]
    | Biwhile (_, _, _, _, cc) -> write_targets_of_bicommand bi_ctxt cc
    | Biassert _ -> WtS.empty, WtS.empty
    | Biassume _ -> WtS.empty, WtS.empty
    | Biupdate (_, _) ->
      (* Modifies the ghost refperm param in Why3 *)
       WtS.empty, WtS.empty

  let rec refine_bicommand bi_ctxt (bicom: bicommand) : bicommand =
    match bicom with
    | Bihavoc_right (x, rf) -> Bihavoc_right (x, rf)
    | Bisplit (c, c') ->
      Bisplit (refine_command bi_ctxt.lft c, refine_command bi_ctxt.rgt c')
    | Bisync ac -> Bisync ac (* cannot contain loops *)
    | Bivardecl (x, x', cc) ->
      Bivardecl (x, x', refine_bicommand bi_ctxt cc)
    | Biseq (cc, cc') ->
      Biseq (refine_bicommand bi_ctxt cc, refine_bicommand bi_ctxt cc')
    | Biif (e, e', cc, cc') ->
      Biif (e, e', refine_bicommand bi_ctxt cc, refine_bicommand bi_ctxt cc')
    | Biif4 (e, e', branches) ->
      Biif4 (e, e', map_fourwayif (refine_bicommand bi_ctxt) branches)
    | Biassume rf -> Biassume rf
    | Biassert rf -> Biassert rf
    | Biupdate (x, x') -> Biupdate (x, x')
    | Biwhile (e, e', ag, wspec, cc) ->
      let lwrs = write_targets bi_ctxt.lft (projl cc) in
      let rwrs = write_targets bi_ctxt.rgt (projr cc) in
      let leff, reff = wspec.biwframe in
      let leff = refine_effect leff lwrs in
      let reff = refine_effect reff rwrs in
      let wspec = {wspec with biwframe = (leff, reff)} in
      Biwhile (e, e', ag, wspec, refine_bicommand bi_ctxt cc)

  let dest_bimeth_def = function Bimethod (decl, cc) -> (decl, cc)

  let refine_bispec (bspec: bispec) (ls, rs) : bispec =
    let wo_effs = filter (function Bieffects _ -> false | _ -> true) bspec in
    let leffs, reffs = bispec_effects bspec in
    let leffs' = refine_effect leffs ls in
    let reffs' = refine_effect reffs rs in
    wo_effs @ [Bieffects (leffs', reffs')]

  let refine_bimeth_def bi_ctxt (bm: bimeth_def) : bi_ctxt * bimeth_def =
    let decl, cc = dest_bimeth_def bm in
    let leffs, reffs = bispec_effects decl.bimeth_spec in
    let lspec'd, rspec'd = map_pair write_targets_of_effect (leffs,reffs) in
    let name = decl.bimeth_name in
    let bimeth_wrs = M.add name (lspec'd, rspec'd) bi_ctxt.bimeth_wrs in
    let bi_ctxt = {bi_ctxt with bimeth_wrs} in
    match cc with
    | None -> bi_ctxt, Bimethod (decl, None)
    | Some cc ->
      let lwts, rwts = write_targets_of_bicommand bi_ctxt cc in
      let bimeth_spec = refine_bispec decl.bimeth_spec (lwts, rwts) in
      let bimeth_wrs = M.add name (lwts, rwts) bi_ctxt.bimeth_wrs in
      let bi_ctxt = {bi_ctxt with bimeth_wrs} in
      bi_ctxt, Bimethod ({decl with bimeth_spec}, Some (refine_bicommand bi_ctxt cc))

  let refine_bimodule bi_ctxt (bm: bimodule_def) : bi_ctxt * bimodule_def =
    let bi_ctxt, bimdl_elts = foldl (fun elt (bi_ctxt, elts) ->
        match elt with
        | Bimdl_mdef m ->
          let bi_ctxt, m' = refine_bimeth_def bi_ctxt m in
          bi_ctxt, Bimdl_mdef m' :: elts
        | _ -> bi_ctxt, elt :: elts
      ) (bi_ctxt, []) bm.bimdl_elts in
    bi_ctxt, {bm with bimdl_elts = rev bimdl_elts}

  let refine (ctbl, penv) =
    let ini_ctxt = {ctbl = ctbl; meth_wrs = M.empty} in
    let ini_bi_ctxt = {lft = ini_ctxt; rgt = ini_ctxt; bimeth_wrs = M.empty} in
    let deps = Deps.dependencies penv in
    let progs = map (fun i -> (i, M.find i penv)) deps in
    let loop (name, prog) (ctxt, bi_ctxt, progs) =
      match prog with
      | Unary_module m ->
        let ctxt', m = refine_module ctxt m in
        ctxt', bi_ctxt, M.add name (Unary_module m) progs
      | Unary_interface i ->
        let ctxt', i = refine_interface ctxt i in
        ctxt', bi_ctxt, M.add name (Unary_interface i) progs
      | Relation_module bm ->
        (* Update the current bi_ctxt with the current unary context *)
        let union_ctxt ctx1 ctx2 =
          (* NOTE: combine should return Some v' if we want to prioritize
             bindings in ctxt and not bi_ctxt.lft, bi_ctxt.rgt. *)
          let combine k v v' = Some v in
          let meth_wrs = M.union combine ctx1.meth_wrs ctx2.meth_wrs in
          { ctbl = ctx1.ctbl; meth_wrs } in
        let lft = union_ctxt bi_ctxt.lft ctxt in
        let rgt = union_ctxt bi_ctxt.rgt ctxt in
        let bi_ctxt = {bi_ctxt with lft; rgt} in
        let bi_ctxt, bm = refine_bimodule bi_ctxt bm in
        ctxt, bi_ctxt, M.add name (Relation_module bm) progs in
    let _, _, progs = foldl loop (ini_ctxt, ini_bi_ctxt, M.empty) progs in
    progs

end


(* -------------------------------------------------------------------------- *)
(* Pre-agreement compatibility                                                *)
(* -------------------------------------------------------------------------- *)

(* TODO: extend_bimodule and extend may not be used because of changes in how
   side conditions of rMLink are treated.  These functions can be removed, and
   Pre_agreement_compat can only export mk_lemma. *)
module Pre_agreement_compat : sig
  (* mk_lemma bnd coupling meth returns the pre-agreement compatibility lemma
     for method meth.meth_name with respect to coupling and bnd. *)
  val mk_lemma : boundary_decl -> ident -> meth_decl -> named_rformula
  val extend_bimodule : penv -> bimodule_def -> bimodule_def
  val extend : penv -> penv
end = struct

  (* derive_pre_agreement returns
     Both (P) ==> <> Agree(rds(n)\bnd+) /\ <> R ==> <> (Agree(rds(n)\bnd+) /\ R)

     where P is the precondition, R is the coupling, n is the method's effect,
     and bnd is the imported boundary.
   *)
  let derive_pre_agreement precond eff bnd coupling : rformula =
    let eff = subtract (rds eff) (eff_of_bnd (bnd_plus bnd)) in
    let agr = agreement_eff eff in
    let coupling = Rprimitive {name=coupling; left_args=[]; right_args=[]} in
    let later_agr = Rlater agr and later_coupling = Rlater coupling in
    let later_agr_coupling = Rlater (Rconn (Ast.Conj, agr, coupling))
    in rimp_list [Rboth precond; later_agr; later_coupling; later_agr_coupling]

  let rec mk_pre_agreement_lemma bnd coupling meth_decl : named_rformula =
    let {meth_name; meth_spec; params} = meth_decl in
    let eff = spec_effects meth_spec in
    let precond = try fconj_list (spec_preconds meth_spec) with _ -> Ftrue in
    let lem_name = Ast.Id (id_name meth_name.node ^ "_pre_agreement") in
    let lem_inner = derive_pre_agreement precond eff bnd coupling in
    let lem_body = quantify_over_meth_params params lem_inner in
    { kind = `Lemma;
      biformula_name = lem_name;
      biparams = ([], []);
      body = lem_body;
      is_coupling = false }

  and quantify_over_meth_params meth_params body : rformula =
    let rec rqbinders_of_params = function
      | [] -> ([], [])
      | {param_name; is_non_null} :: rest ->
        let ps, qs = rqbinders_of_params rest in
        let p = {name=param_name; in_rgn=None; is_non_null} in
        (p :: ps, p :: qs)
    in
    Rquant (Ast.Forall, rqbinders_of_params meth_params, body)

  let mk_lemma = mk_pre_agreement_lemma

  let find_interface_meth_decl penv mdl_name meth_name : meth_decl option =
    let mdl = find_unary_module penv mdl_name in
    let intr = find_unary_interface penv mdl.mdl_interface in
    let get_meth_spec = function
      | Intr_mdecl ({meth_name = name} as m) ->
        if name.node = meth_name then Some m else None
      | _ -> None
    in first_opt get_meth_spec intr.intr_elts

  let bimdl_unary_meth_decls penv bimdl : meth_decl list =
    let left_mdl_name = bimdl.bimdl_left_impl in
    let get_meth_decl = function
      | Bimdl_mdef (Bimethod ({bimeth_name}, _)) ->
        (* NOTE: Relies on knowing that a bimethods name matches the name of the
           two unary methods it's relating. *)
        find_interface_meth_decl penv left_mdl_name bimeth_name
      | _ -> None
    in filtermap get_meth_decl bimdl.bimdl_elts

  let extend_bimodule penv bimdl =
    let mk_formula l = Bimdl_formula l in
    let meth_decls = bimdl_unary_meth_decls penv bimdl in
    let coupling = bimodule_coupling bimdl in
    let bnd = Boundary_info.overall_boundary bimdl.bimdl_name in
    match coupling with
    | None -> bimdl
    | Some {biformula_name = inv} ->
      let mk_lem = mk_formula % mk_pre_agreement_lemma bnd inv in
      let lemmas = map mk_lem meth_decls in
      { bimdl with bimdl_elts = bimdl.bimdl_elts @ lemmas }

  let extend penv =
    let step name mdl prog = match mdl with
      | Unary_interface i -> M.add name (Unary_interface i) prog
      | Unary_module m -> M.add name (Unary_module m) prog
      | Relation_module bm ->
        let bm' = extend_bimodule penv bm in
        M.add name (Relation_module bm') prog
    in M.fold step penv M.empty

end


(* -------------------------------------------------------------------------- *)
(* Post-agreement compatibility                                               *)
(* -------------------------------------------------------------------------- *)

(* TODO: this is very similar to Pre_agreement_compat; refactor *)
(* [Sep-30-22] DEPRECATED
module Post_agreement_compat : sig
  val mk_lemma : boundary_decl -> ident -> meth_decl -> named_rformula
end = struct

  (* derive_post_agreement S n bnd R is

     Both(S) ==> <> (forall s_alloc|s_alloc. E[s_alloc]) /\ <> R
             ==> <> ((forall s_alloc|s_alloc. E[s_alloc]) /\ R)

       where E[s] = (rd(alloc\s)`any, Asnap(n))\bnd

     Additional snapshot variables introduced by Asnap(n) are universally
     quantified over.
  *)
  let derive_post_agreement postcond eff bnd coupling : rformula =
    let coupling = Rprimitive {name=coupling; left_args=[]; right_args=[]} in
    let effpost = agreement_effpost ~quantify:true eff bnd in
    let later_agr = Rlater effpost and later_coupling = Rlater coupling in
    let later_agr_coupling = Rlater (Rconn (Ast.Conj, effpost, coupling)) in
    rimp_list [Rboth postcond; later_agr; later_coupling; later_agr_coupling]

  let rec mk_lemma bnd coupling meth_decl =
    let {meth_name; meth_spec; params} = meth_decl in
    let eff = spec_effects meth_spec in
    let postcond = try fconj_list (spec_postconds meth_spec) with _ -> Ftrue in
    let lem_name = Ast.Id (id_name meth_name.node ^ "_post_agreement") in
    let lem_inner = derive_post_agreement postcond eff bnd coupling in
    let lem_body = quantify_over_meth_params params lem_inner in
    { kind = `Lemma;
      biformula_name = lem_name;
      biparams = ([], []);
      body = lem_body;
      is_coupling = false }

  and quantify_over_meth_params meth_params body : rformula =
    let rec rqbinders_of_params = function
      | [] -> ([], [])
      | {param_name; is_non_null} :: rest ->
         let ps,qs = rqbinders_of_params rest in
         let p = {name=param_name; in_rgn=None; is_non_null} in
         (p::ps, p::qs)
    in Rquant(Ast.Forall, rqbinders_of_params meth_params, body)
end
 *)


(* -------------------------------------------------------------------------- *)
(* Agreement compatibility (simplified/afoot check)                           *)
(* -------------------------------------------------------------------------- *)

module Acompat_simplified = struct

  exception Not_applicable of rformula

  let footl, footr =
    let rec foot rf side = match rf with
      | Rboth (Ftrue) | Rboth (Ffalse) -> Econst (Eemptyset -: Trgn)
      | Rbiequal (f,f') when f.ty = Trgn -> (side (f,f')).node
      | Rbiequal (f,f') when is_class_ty f.ty -> Esingleton (side (f,f'))
      | Rbiequal _ -> Econst (Eemptyset -: Trgn)
      | Rconn (Conj,rf1,rf2) ->
        let e1 = foot rf1 side in
        let e2 = foot rf2 side in
        Ebinop (Union, e1 -: Trgn, e2 -: Trgn)
      | Ragree (g,f) -> Ebinop (Union, g, Eimage(g,f) -: Trgn)
      | _ -> raise (Not_applicable rf)
    in
    (fun rf -> foot rf fst -: Trgn), (fun rf -> foot rf snd -: Trgn)

  let disjointness_check postcond rf rf' =
    let left_check =
      let r1 = footl rf in
      let r2 = footl rf' in
      Rleft (Fdisjoint (r1, r2)) in
    let right_check =
      let r1 = footr rf in
      let r2 = footr rf' in
      Rright (Fdisjoint (r1, r2)) in
    let check = Rconn (Conj, left_check, right_check)
    in Rconn (Imp, Rboth postcond, check)

  let disjointness_of_regions_under postcond (l_rgn,r_rgn) (l_rgn',r_rgn') =
    let lcheck = Rleft (Fdisjoint (l_rgn, l_rgn')) in
    let rcheck = Rright (Fdisjoint (r_rgn, r_rgn')) in
    Rconn (Imp, Rboth postcond, Rconn (Conj, lcheck, rcheck))

  (* effpost bnd eff = (rd (alloc \ s_alloc)`any, Asnap(eff)) \ bnd *)
  let effpost bnd eff =
    let alloc = Evar (Ast.Id "alloc" -: Trgn) -: Trgn in
    let s_alloc = Evar (Ast.Id "s_alloc" -: Trgn) -: Trgn in
    let diffalloc = Ebinop (Diff, alloc, s_alloc) -: Trgn in
    let diffeff =
      let desc = Effimg(diffalloc, Ast.Id "any" -: Tdatagroup) -: Trgn in
      [{effect_kind = Read; effect_desc = desc}] in
    let asnap_eff = Snap.asnap' eff in
    let bnd_eff = eff_of_bnd bnd
    in subtract (nub (diffeff @ asnap_eff)) bnd_eff

  let agreement_effpost bnd eff : rformula =
    let eff = effpost bnd eff in
    agreement_eff eff

end


(* -------------------------------------------------------------------------- *)
(* Build linked module with proof obligations of rMLink                       *)
(* -------------------------------------------------------------------------- *)

module Derive_linked_module : sig
  val add_linked_module : Ctbl.t * penv -> penv
end = struct

  let main_module_name = ident "Main"

  let main_interface_name = ident "MAIN"

  (* Check if a module called "Main" exists in penv *)
  let does_main_exist penv = can (find_unary_module penv) main_module_name

  (* Get the module_def for module "Main" *)
  let find_main_module penv = find_unary_module penv main_module_name

  (* Check if a method called "main" exists in a module called "Main" *)
  let does_main_method_exist penv =
    does_main_exist penv && begin
      let meths = module_methods (find_main_module penv) in
      mem (ident "main") meths
    end

  (* Get the meth_def for "main" in module "Main" *)
  let find_main_method penv : meth_def =
    let mdl = find_main_module penv in
    let p = function
      | Mdl_mdef (Method ({meth_name={node=Ast.Id "main"}},_) as m) -> Some m
      | _ -> None
    in first p mdl.mdl_elts

  (* Given a method def, obtain the preconditions *)
  let find_preconditions meth : formula list =
    let Method ({meth_spec}, _) = meth in
    spec_preconds meth_spec

  type import_info = {imported: ident; related_by: ident}

  let find_relating_bimodules main : import_info list =
    let imports = module_imports main in
    let walk curr rest = match curr with
      | {import_name; related_by=Some bimdl} ->
        {imported = import_name; related_by = bimdl} :: rest
      | _ -> rest
    in foldr walk [] imports

  type invariants = {
    pub: named_formula list;
    priv: (named_formula list * named_formula list);
    coupling: named_rformula list;
  }

  let join_invariants i1 i2 =
    let {pub = pub1; priv = (lpriv1, rpriv1); coupling = coupling1} = i1 in
    let {pub = pub2; priv = (lpriv2, rpriv2); coupling = coupling2} = i2 in
    let pub = pub1 @ pub2 and priv = (lpriv1 @ lpriv2, rpriv1 @ rpriv2) in
    let coupling = coupling1 @ coupling2 in
    {pub; priv; coupling}

  (* Find all invariants that must be implied by main's precondition (or the
     precondition of main's local equivalence spec for coupling invariants). *)
  let rec find_relevant_invariants penv : invariants =
    let main = find_main_module penv in
    let bimdls = find_relating_bimodules main in
    let empty = {pub = []; priv = ([], []); coupling = []} in
    let walk {imported; related_by} inv =
      let inv2 = find_invariants penv imported related_by in
      join_invariants inv inv2
    in foldr walk empty bimdls

  and find_invariants penv interface bimdl : invariants =
    let interface = find_unary_interface penv interface in
    let bimdl = find_relation_module penv bimdl in
    let {bimdl_left_impl=l; bimdl_right_impl=r} = bimdl in
    let left_mdl, right_mdl = map_pair (find_unary_module penv) (l, r) in
    let pubinv = Option.to_list (interface_public_invariant interface) in
    let lpriv = Option.to_list (module_private_invariant left_mdl) in
    let rpriv = Option.to_list (module_private_invariant right_mdl) in
    let relinv = Option.to_list (bimodule_coupling bimdl) in
    { pub = pubinv; priv = (lpriv, rpriv); coupling = relinv }

  let make_local_equiv_method ctbl penv meth : bimeth_def =
    let meth_name = meth.meth_name.node in
    let bispec = LocEq.derive_locEq ctbl penv meth_name in
    let bimeth_body = None in
    let bimeth_decl =
      { bimeth_name = meth_name;
        bimeth_left_params = meth.params;
        bimeth_right_params = meth.params;
        result_ty = dup_pair meth.result_ty;
        result_is_non_null = dup_pair meth.result_is_non_null;
        bimeth_can_diverge = false; (* TODO: is this what we want? *)
        bimeth_spec = bispec }
    in Bimethod (bimeth_decl, bimeth_body)

  let methods_in_main penv : meth_decl list =
    let main = find_main_module penv in
    let elts = main.mdl_elts in
    filtermap (function Mdl_mdef(Method(m,_)) -> Some m | _ -> None) elts

  let gen_module_name =
    let mk_name id n = ident (id_name id ^ string_of_int n) in
    let stamp = ref 0 in
    let rec loop name known =
      let currentstamp = !stamp in
      if mem name known
      then (incr stamp; loop (mk_name name currentstamp) known)
      else name
    in
    fun (penv: penv) name -> loop (ident name) (map fst (M.bindings penv))

  let build_link_module_methods ctbl penv : bimodule_elt list =
    let meths = methods_in_main penv in
    let bimeths = map (make_local_equiv_method ctbl penv) meths
    in map (fun m -> Bimdl_mdef m) bimeths

  let rec build_link_module_imports penv : bimodule_elt list =
    let main_module = find_main_module penv in
    let bimodules = find_relating_bimodules main_module in
    let bimodules = map (fun {related_by=b} -> b) bimodules in
    map mk_import bimodules

  and mk_import name =
    let import name =
      { import_kind = Iregular;
        import_name = name;
        import_as = None;
        related_by = None}
    in Bimdl_import (import name)

  (* Each lemma in result states that main's precondition (or its locEq
     precondition) implies any unary (or relational invariant) found in any
     related set of modules imported by main.
  *)
  let rec build_link_module_invariant_lemmas ctbl penv : bimodule_elt list =
    if not (does_main_method_exist penv) then [] else
      let invs = find_relevant_invariants penv in
      let Method (main_decl, main_body) as main_meth = find_main_method penv in
      let main_name = main_decl.meth_name.node in
      let params = main_decl.params in
      let meth_preconds = find_preconditions main_meth in
      let loc_eq = LocEq.derive_locEq ctbl penv main_name in
      let loc_eq_preconds = bispec_preconds loc_eq in
      let pub = public_invariants_hold_under params meth_preconds invs.pub in
      let priv = private_invariants_hold_under params meth_preconds invs.priv in
      let rel = couplings_hold_under params loc_eq_preconds invs.coupling
      in pub @ priv @ rel

  and public_invariants_hold_under params preconds pubinvs : bimodule_elt list =
    let mk_name pubinv =
      let name = pubinv.formula_name.node in
      ident (id_name name ^ "_holds_in_main") in (* FIXME: possible name clash? *)
    let mk_body pubinv =
      let invname = pubinv.formula_name in
      let call_node = Fexp (Ecall (invname, []) -: Tprop) in
      let inner = Rboth (mk_fimplies preconds call_node) in
      universally_quantify_over_params params inner
    in map (uncurry mk_bimodule_lemma % fork (mk_name, mk_body)) pubinvs

  and private_invariants_hold_under params preconds (lprivs, rprivs)
    : bimodule_elt list =
    let mk_name side privinv =
      let name = privinv.formula_name.node in
      match side with
      | `Left -> ident ("left_" ^ id_name name ^ "_holds_in_main")
      | `Right -> ident ("right_" ^ id_name name ^ "_holds_in_main") in
    let mk_body side privinv =
      let invname = privinv.formula_name in
      let call_node = Fexp (Ecall (invname, []) -: Tprop) in
      let inner = match side with
        | `Left -> Rleft (mk_fimplies preconds call_node)
        | `Right -> Rright (mk_fimplies preconds call_node) in
      universally_quantify_over_params params inner in
    let mk side = uncurry mk_bimodule_lemma % fork (mk_name side, mk_body side)
    in map (mk `Left) lprivs @ map (mk `Right) rprivs

  and couplings_hold_under params loc_eq_preconds couplings
    : bimodule_elt list =
    let mk_name coupling =
      let name = coupling.biformula_name in
      ident (id_name name ^ "_holds_in_main") in
    let mk_body coupling =
      let invname = coupling.biformula_name in
      let call_node = Rprimitive {name=invname; left_args=[]; right_args=[]} in
      let inner = mk_rimplies loc_eq_preconds call_node in
      universally_quantify_over_params params inner
    in map (uncurry mk_bimodule_lemma % fork (mk_name, mk_body)) couplings

  and universally_quantify_over_params params rfrm =
    let rec build_term rfrm params = match params with
      | [] -> rfrm
      | {param_name=p} :: ps ->
        let lbind = {name = p; in_rgn = None; is_non_null = false} in
        let rbind = {name = p; in_rgn = None; is_non_null = false} in
        Rquant (Forall, ([lbind], [rbind]), build_term rfrm ps)
    in build_term rfrm params

  and mk_bilemma lem_name lem_body : named_rformula =
    { kind = `Lemma;
      biformula_name = lem_name;
      biparams = ([], []);
      body = lem_body;
      is_coupling = false; }

  and mk_bimodule_lemma lem_name lem_body : bimodule_elt =
    Bimdl_formula (mk_bilemma lem_name lem_body)

  and mk_fimplies ants frm = fimp_list (ants @ [frm])

  and mk_rimplies ants rfrm = rimp_list (ants @ [rfrm])

  (* DEPRECATED *)
  let rec build_link_module_pre_agreements penv : bimodule_elt list =
    if not (does_main_exist penv) then [] else
      let main = find_main_module penv in
      let imports = find_relating_bimodules main in
      let bimdls = map (fun {related_by} -> related_by) imports in
      let bimdls = map (find_relation_module penv) bimdls in
      let lems = concat_map (build_pre_agreement_lemmas penv) bimdls in
      map (fun l -> Bimdl_formula l) lems

  (* DEPRECATED *)
  and build_pre_agreement_lemmas penv bimdl : named_rformula list =
    let bnd = Boundary_info.overall_boundary bimdl.bimdl_name in
    let coupling = bimodule_coupling bimdl in
    let left_mdl = find_unary_module penv bimdl.bimdl_left_impl in
    let interface = find_unary_interface penv left_mdl.mdl_interface in
    let mdecls = interface_meth_decls interface in
    match coupling with
    | None -> []
    | Some c -> map (Pre_agreement_compat.mk_lemma bnd c.biformula_name) mdecls

  (* DEPRECATED *)
  (* let rec build_link_module_post_agreements penv : bimodule_elt list =
    if not (does_main_exist penv) && not (does_main_method_exist penv) then []
    else begin
        let get_bimdl {related_by} = related_by in
        let main = find_main_module penv in
        let Method (mdecl,_) = find_main_method penv in
        let imports = find_relating_bimodules main in
        let bimdls = map (find_relation_module penv % get_bimdl) imports in
        let lems = concat_map (build_post_agreement_lemmas penv mdecl) bimdls in
        map (fun l -> Bimdl_formula l) lems
      end *)

  (* DEPRECATED *)
  (* and build_post_agreement_lemmas penv mdecl bimdl : named_rformula list =
    let bnd = Boundary_info.overall_boundary bimdl.bimdl_name in
    let coupling = bimodule_coupling bimdl in
    match coupling with
    | None -> []
    | Some c -> [Post_agreement_compat.mk_lemma bnd c.biformula_name mdecl] *)

  let build_link_module ctbl penv : ident * bimodule_def =
    let module_name = gen_module_name penv "Main_Link" in
    let imports = build_link_module_imports penv in
    let meths = build_link_module_methods ctbl penv in
    let inv_lemmas = build_link_module_invariant_lemmas ctbl penv in
    (* let pre_agreements = build_link_module_pre_agreements penv in
     * let post_agreements = build_link_module_post_agreements penv in *)
    let bimdl_elts = imports @ inv_lemmas @ meths in
    (* let bimdl_elts =
     *   imports @ inv_lemmas @ pre_agreements @ post_agreements @ meths in *)
    let bimdl =
      { bimdl_name = module_name;
        bimdl_left_impl = main_module_name;
        bimdl_right_impl = main_module_name;
        bimdl_elts = bimdl_elts }
    in module_name, bimdl

  let add_linked_module (ctbl, penv) =
    if does_main_exist penv then
      let name, link_mdl = build_link_module ctbl penv in
      let link_mdl = Relation_module link_mdl in
      let penv = M.add name link_mdl penv
      in Boundary_info.add penv name link_mdl; penv
    else penv

end


(* -------------------------------------------------------------------------- *)
(* Add a `diverges' clause to specs of methods that may diverge               *)
(* -------------------------------------------------------------------------- *)

(* [2024-08-18] TODO: Add [@vc:divergent] to each generated function instead.

   The [Update_divergence_info] module is NOT required!  This module processes
   source programs and generates a diverges clause for each method that
   contains a loop so that termination need not be proved.  We can't annotate
   every method with a diverges clause because it's an error for a WhyML
   function without variant-free loops to be marked as diverging.  The
   function [Update_divergence_info.update] figures out what methods can be
   marked as diverging and updates specs accordingly.

   The point of this module is to ensure users never have to prove termination
   of generated WhyML functions.  Care needs to be taken to not raise any Why3
   errors when flagging WhyML functions as diverging.

   However, Why3 supports a [@vc:divergent] annotation which disables the
   termination check and also doesn't raise an error if the annotated function
   doesn't include a variant-free loop!  We should be using this.
*)

module Update_divergence_info : sig
  val update : penv -> penv
end = struct

  (* A command can diverge if it includes a loop or a call to a method
     that can diverge *)
  let can_command_diverge (div_meths: ident list) (c: command) : bool =
    let can_exp_diverge = function
      | {node = Ecall (m, _)} -> elem_of div_meths m.node
      | _ -> false in
    let can_atomic_command_diverge = function
      | Assign (_, e) -> can_exp_diverge e
      | Call (_, m, _) -> elem_of div_meths m.node
      | Field_update (_, _, e) -> can_exp_diverge e
      | Array_access (_, _, e) -> can_exp_diverge e
      | Array_update (_, e1, e2) -> can_exp_diverge e1 || can_exp_diverge e2
      | New_array (_, _, e) -> can_exp_diverge e
      | _ -> false in
    let rec aux = function
      | Acommand ac -> can_atomic_command_diverge ac
      | Vardecl (_, _, _, c) -> aux c
      | Seq (c1, c2) -> aux c1 || aux c2
      | If (_, c1, c2) -> aux c1 || aux c2
      | While _ -> true
      | Assume _ | Assert _ -> false
    in aux c

  let update_meth_def div_meths (m: meth_def) : (meth_def * bool) =
    let Method (mdecl, c) = m in
    match c with
    | Some c ->
      if can_command_diverge div_meths c
      then Method ({mdecl with can_diverge = true}, Some c), true
      else Method (mdecl, Some c), false
    | None -> Method (mdecl, c), false

  (* Since we don't have a notion of "bicode", a bicommand can diverge if one
     of it's projections can. *)
  let can_bicommand_diverge div_meths (c: bicommand) : bool =
       can_command_diverge div_meths (projl c)
    || can_command_diverge div_meths (projr c)

  let update_bimeth_def div_meths (m: bimeth_def) : (bimeth_def * bool) =
    match m with
    | Bimethod (mdecl, Some c) when can_bicommand_diverge div_meths c ->
      Bimethod ({mdecl with bimeth_can_diverge = true}, Some c), true
    | _ -> m, false

  let meth_name (m: meth_def) : ident =
    match m with Method (mdecl, _) -> mdecl.meth_name.node

  let bimeth_name (m: bimeth_def) : ident =
    match m with Bimethod (bmdecl, _) -> bmdecl.bimeth_name

  let update_module_def (mdl: module_def) : module_def =
    let rec walk elt (div_meths, acc) = match elt with
      | Mdl_mdef mdef ->
        let mdef', div = update_meth_def div_meths mdef in
        let name = meth_name mdef' in
        let div_meths = if div then name :: div_meths else div_meths in
        (div_meths, Mdl_mdef mdef' :: acc)
      | elt -> (div_meths, elt :: acc)
    in
    {mdl with mdl_elts = snd (foldr walk ([], []) mdl.mdl_elts)}

  let update_bimodule_def (bmdl: bimodule_def) : bimodule_def =
    let rec walk elt (div_meths, acc) = match elt with
      | Bimdl_mdef mdef ->
        let mdef', div = update_bimeth_def div_meths mdef in
        let name = bimeth_name mdef' in
        let div_meths = if div then name :: div_meths else div_meths in
        (div_meths, Bimdl_mdef mdef' :: acc)
      | elt -> (div_meths, elt :: acc)
    in
    {bmdl with bimdl_elts = snd (foldr walk ([], []) bmdl.bimdl_elts)}

  let update : penv -> penv = M.map (function
    | Unary_module mdl -> Unary_module (update_module_def mdl)
    | Relation_module bimdl -> Relation_module (update_bimodule_def bimdl)
    | other -> other)
end


(* -------------------------------------------------------------------------- *)
(* All-exists mode transformations                                            *)
(* -------------------------------------------------------------------------- *)

(* [2024-10-29] A new design for transformations.  The [Map_penv]
   module should include functions that map over other types, e.g.,
   commands, effects, etc. *)
module Map_penv : sig
  val map_bicommand : (bicommand -> bicommand) -> penv -> penv
end = struct
  let map_bicommand (f: bicommand -> bicommand) penv : penv =
    let on_bimeth_def mdef =
      let Bimethod (bimdecl, com) = mdef in
      Bimethod (bimdecl, Option.map f com) in
    let on_bimodule_elt = function
      | Bimdl_mdef m -> Bimdl_mdef (on_bimeth_def m)
      | elt -> elt in
    let on_bimodule_def b =
      {b with bimdl_elts = map on_bimodule_elt b.bimdl_elts} in
    let walk = function
      | Relation_module bm ->
        Relation_module (on_bimodule_def bm)
      | m -> m in
    M.map walk penv
end

module All_existify : sig
  val all_existify : penv -> penv
end = struct
  let all_existify penv =
    assert !all_exists_mode;
    if !all_exists_mode then Map_penv.map_bicommand all_existify penv else penv
end


(* -------------------------------------------------------------------------- *)
(* Driver                                                                     *)
(* -------------------------------------------------------------------------- *)

let process ctbl penv =
  (* Add invariants (public/private/coupling) to method specs; further, for each
     public method conjoin its interface spec to its module spec. *)
  let penv = Expand_method_spec.expand penv in

  (* Flag methods that may diverge---contain either a loop or call a method
     that may diverge. *)
  let penv = Update_divergence_info.update penv in

  (* Expand datagroups in effects, boundaries, and image expressions.  Note that
     the current version of WhyRel only supports the "any" datagroup. *)
  let penv = Resolve_datagroups.resolve (ctbl, penv) in

  (* Normalize effects in specs and normalize module boundaries. *)
  let penv = Normalize_effects.normalize penv in

  (* Rename locals that shadow global variables.  This pass is required to
     ensure the encap check does not fail because of shadowing---if a global
     variable, part of some modules boundary, is shadowed by a local variable,
     then any write to the local variable may cause the encap check to fail.

     If however, we kept track of additional information during the encap check,
     we would not need this pass. *)
  let penv = Rename_Locals.rename penv in

  (* Cache module boundaries.  Information about module boundaries is required
     by subsequent passes and at some point in the past it seemed nice to have
     this saved in a mutable map. *)
  let () = Boundary_info.run penv in

  (* Extend each method spec to include the methods boundary monotonicity, or
     Bmon, spec. *)
  let penv = Boundary_mono_spec.extend_specs penv in

  (* Perform the encapsulation check.  If statically determined to fail, exit
     the program.  If the -no-encap flag is passed, the check does not take
     place. *)
  let penv = Encap_check.run_maybe_exit (ctbl, penv) in

  (* For each bimodule in penv, derive a biinterface and add it to penv.
     A biinterface is a bimodule where each bimethod is not given an
     implementation.  Further, the biinterface hides the designated coupling
     relation. *)
  let penv = Derive_biinterface.extend penv in

  (* Simplify effects after normalization *)
  let penv = Simplify_effects.simplify (ctbl, penv) in

  (* Refine write effects of implementations. *)
  let penv = Refine_writes.refine (ctbl, penv) in

  (* Add Main_Link module with side conditions of rMLink. *)
  let penv = Derive_linked_module.add_linked_module (ctbl, penv) in

  (* Transform biprograms if in all_exists mode *)
  let penv = All_existify.all_existify penv in

  penv
