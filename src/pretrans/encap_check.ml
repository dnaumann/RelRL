(** encap_check.ml -- encapsulation check *)

open Astutil
open Annot
open Annot.Norm
open Lib


(* -------------------------------------------------------------------------- *)
(* Exceptions, flags, and utilities                                           *)
(* -------------------------------------------------------------------------- *)

exception Encap_check_fail of (atomic_command, exp t) result

let do_encap_check = ref true

let encap_debug = ref false

let alloc_var = Ast.Id "alloc" -: Trgn

let rw_alloc = [rdvar alloc_var; wrvar alloc_var]


(* -------------------------------------------------------------------------- *)
(* Effect separation                                                          *)
(* -------------------------------------------------------------------------- *)

(* Precondition for computing separator *)
let separator_pre (e: effect) =
  Resolve_datagroups.is_resolved e

let check_separator_pre e : unit =
  if separator_pre e then ()
  else
    let e = pp_as_string Pretty.pp_effect e in
    failwith ("Malformed effect: " ^ e)

module FrmSet = Set.Make (struct
    type t = formula
    let compare = compare
  end)

let contains_var (eff: effect_desc list) (x: ident t) =
  let p = function
    | Effvar y -> x.node = y.node && x.ty = y.ty
    | Effimg _ -> false in
  exists p eff

let find_img_field (eff: effect_desc list) (f: ident t) =
  let p = function
    | Effvar y -> false
    | Effimg (_, g) -> f.node = g.node && f.ty = g.ty in
  match find p eff with Effimg (g,_) -> Some g | _ | exception _ -> None


(* separator e1 e2 = frm

   If e1 and e2 do not contain any datagroups and are normalized,
   then frm = e1 % e2.  Note that this is identical to rds(e1) % wrs(e2).

   frm is a conjunction of true's, false's, and disjointness formulas.
*)
let separator (e1: effect) (e2: effect) : formula =
  (* assert (separator_pre e1 && separator_pre e2); *)
  (* TODO: can we avoid normalizing effects here? *)
  let e1 = Norm.normalize e1 in
  let e2 = Norm.normalize e2 in

  let () = check_separator_pre e1 in
  let () = check_separator_pre e2 in

  let mk_conj f1 f2 = Fconn (Conj, f1, f2) in

  (* When computing e1 % e2, it is possible that the same disjointness
     assertion will be repeated.  The loop function below uses FrmSet (set of
     formulas) to avoid an issue in which long chains of conjuncts of the same
     term are generated. *)
  let rec loop fset wrs rds = match rds with
    | [] -> fset
    | Effvar x :: rest ->
      if contains_var wrs x
      then loop (FrmSet.add Ffalse fset) wrs rest
      else loop (FrmSet.add Ftrue fset) wrs rest
    | Effimg (g,f) :: rest ->
      match find_img_field wrs f with
      | None -> loop (FrmSet.add Ftrue fset) wrs rest
      | Some g' -> loop (FrmSet.add (Fdisjoint (g,g')) fset) wrs rest in

  let e1 = rds e1 and e2 = wrs e2 in
  let e1, e2 = map_pair (List.map (fun e -> e.effect_desc.node)) (e1, e2) in
  let res = loop FrmSet.empty e2 e1 in
  foldr mk_conj Ftrue (FrmSet.elements res)

(* Simplify the result of separator e1 e2.

   Rewrite true /\ H and H /\ true to H
   Rewrite false /\ H and H /\ false to false
   Rewrite (G # G) to false
   Rewrite H /\ H to H
   Rewrite {x} # G to not (x in G)
   Rewrite G # {x} to not (x in G)
   Rewrite {x} # {y} to x <> y
*)
let rec simplify_separator_formula frm =
  match frm with
  | Ftrue -> Ftrue
  | Ffalse -> Ffalse
  | Fconn (Conj, f1, f2) ->
    let f1' = simplify_separator_formula f1 in
    let f2' = simplify_separator_formula f2 in
    begin match f1', f2' with
      | Ftrue, h  | h, Ftrue -> h
      | Ffalse, h | h, Ffalse -> Ffalse
      | f, f' when f = f' -> f
      | _, _ -> Fconn (Conj, f1', f2')
    end
  | Fdisjoint ({node=Esingleton e}, {node=Esingleton e'}) ->
     Fexp ({node = Ebinop(Nequal, e, e'); ty = Tbool})
  | Fdisjoint ({node=Esingleton e}, g') -> Fnot (Fmember(e, g'))
  | Fdisjoint (g, {node=Esingleton e}) -> Fnot (Fmember(e, g))
  | Fdisjoint (g, g') when g = g' -> Ffalse
  | _ -> frm

type check_result =
  | Separate
  | Not_separate
  | Separate_if of formula

(* separator_check e1 e2 = res

   res indicates whether e1 % e2 holds.  If we cannot determine this
   statically then res = Separate_if(f) where e1 % e2 holds if f holds.
*)
let separator_check (e1: effect) (e2: effect) : check_result =
  let sep = separator e1 e2 in
  match simplify_separator_formula sep with
  | Ffalse -> Not_separate
  | Ftrue  -> Separate
  | frm    -> Separate_if frm


(* -------------------------------------------------------------------------- *)
(* Organize relevant information about known methods                          *)
(* -------------------------------------------------------------------------- *)

type meth_info = {
  meth_result_ty: ity;
  meth_params: ident t list;
  meth_module: ident;
  meth_effects: effect;
}

type meth_map = meth_info M.t (* maps from identifiers to 'a *)

let meth_map_of_penv prog : meth_map =
  let effects_of_spec =
    concat_filter_map (function Effects e -> Some e | _ -> None) in

  let debug_print mdecl mdl_name =
    Format.fprintf Format.err_formatter
      "Processing method %s in %s: \neffects: @[<hv>%a@]\n"
      (string_of_ident mdecl.meth_name.node)
      (string_of_ident mdl_name)
      Pretty.pp_effect (effects_of_spec mdecl.meth_spec);
    Format.pp_print_flush Format.err_formatter ()
  in

  let interface_methods i =
    let intr_name = i.intr_name in
    let step elt map = match elt with
      | Intr_mdecl mdecl ->
        if !encap_debug then debug_print mdecl intr_name;
        let meth_effects = effects_of_spec mdecl.meth_spec in
        let meth_params = List.map (fun e -> e.param_name) mdecl.params in
        let meth_result_ty = mdecl.result_ty in
        let minfo = {meth_module = intr_name; meth_effects;
                     meth_params; meth_result_ty} in
        M.add mdecl.meth_name.node minfo map
      | _ -> map in
    List.fold_right step i.intr_elts M.empty in

  let module_methods intr_map m =
    let mdl_name = m.mdl_name in
    let step elt map = match elt with
      | Mdl_mdef mdef ->
        let Method (mdecl, _) = mdef in
        let meth_name = mdecl.meth_name.node in
        if M.mem meth_name intr_map then map
        else begin
          if !encap_debug then debug_print mdecl mdl_name;
          let meth_effects = effects_of_spec mdecl.meth_spec in
          let meth_params = List.map (fun e -> e.param_name) mdecl.params in
          let meth_result_ty = mdecl.result_ty in
          let minfo = {meth_module = mdl_name; meth_effects;
                       meth_params; meth_result_ty} in
          M.add meth_name minfo map
        end
      | _ -> map in
    List.fold_right step m.mdl_elts intr_map in

  (* Create partial meth_map from only interfaces in prog *)
  let ini_map = M.fold (fun name frag meth_map ->
      match frag with
      | Unary_interface i ->
        let parmap = interface_methods i in
        M.union (fun _ v _ -> Some v) meth_map parmap
      | _ -> meth_map
    ) prog M.empty in

  (* Create meth_map using modules in prog *)
  M.fold (fun name frag meth_map ->
      match frag with
      | Unary_module m ->
        let parmap = module_methods ini_map m in
        M.union (fun _ v _ -> Some v) meth_map parmap
      | _ -> meth_map
    ) prog M.empty


(* -------------------------------------------------------------------------- *)
(* Substitution (required when computing the effects of an atomic call)       *)
(* -------------------------------------------------------------------------- *)

(* FIXME: Functionality duplicated in Rename_Locals; consider refactoring. *)
type subst = (ident t * ident t) list

let ( #! ) s x = try List.assoc x s with Not_found -> x

let subst_exp (s: subst) (e: exp t) : exp t =
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
  end -: e.ty in subst e

let subst_effect (s: subst) (e: effect) : effect =
  let rec subst eff = function
    | [] -> eff
    | {effect_desc = {node = Effvar x; ty}; effect_kind} :: rest ->
      let e = {effect_kind; effect_desc = {node = Effvar (s #! x); ty}} in
      subst (e :: eff) rest
    | {effect_desc = {node = Effimg (g, f); ty}; effect_kind} :: rest -> (* G`f *)
      let g' = subst_exp s g in
      let desc = Effimg (g', f) in
      let e = {effect_kind; effect_desc = {node = desc; ty}} in
      subst (e :: eff) rest in
  List.rev (subst [] e)


(* -------------------------------------------------------------------------- *)
(* Compute the effect of an atomic command                                    *)
(* -------------------------------------------------------------------------- *)

(*
   skip           ==> empty effect
   x := e         ==> wr x, ftpt(e)
   x := y.f       ==> wr x, rd y, rd {y}`f
   x.f := e       ==> rd x, wr {x}`f, ftpt(e)
   x := new K     ==> wr x, rw alloc
   x := new K[sz] ==> wr x, rw alloc, ftpt(sz)
   x := a[i]      ==> wr x, rd a, rd {a}`slots, ftpt(i)
   a[i] := e      ==> rd a, wr {a}`slots, ftpt(e)

   m(v1...vn)     ==> get meth effect, subst
*)
let acom_effect (mmap: meth_map) (ctbl: Ctbl.t) (a: atomic_command) : effect =
  match a with
  | Skip -> []
  | Assign (x, e) -> wrvar x :: ftpt_exp e
  | Havoc x -> [wrvar x]
  | Field_deref (x, y, f) -> [wrvar x; rdvar y; rdimg (sngl y) f]
  | Field_update (x, f, e) -> rdvar x :: wrimg (sngl x) f :: ftpt_exp e
  | New_class (x, k) -> wrvar x :: rw_alloc
  | New_array (x, k, sz) -> wrvar x :: rw_alloc @ ftpt_exp sz
  | Array_access (x, a, i) -> begin match a.ty with
      | Tclass cname when Ctbl.is_array_like_class ctbl ~classname:cname ->
        let slots,ty =
          Option.get (Ctbl.array_like_slots_field ctbl ~classname:cname) in
        wrvar x :: rdvar a :: rdimg (sngl a) (slots -: ty) :: ftpt_exp i
      | _ -> invalid_arg "acom_effect: invalid array access"
    end
  | Array_update (a, i, e) -> begin match a.ty with
      | Tclass cname when Ctbl.is_array_like_class ctbl ~classname:cname ->
        let slots,ty =
          Option.get (Ctbl.array_like_slots_field ctbl ~classname:cname) in
        rdvar a :: wrimg (sngl a) (slots -: ty) :: ftpt_exp e
      | _ -> invalid_arg "acom_effect: invalid array update"
    end
  | Call (x, m, es) ->
    let wr_to_x = match x with None -> [] | Some x -> [wrvar x] in
    (* If m is a math function, then it is not present in mmap. *)
    try
      let {meth_effects; meth_params; meth_result_ty} = M.find m.node mmap in
      let subst = List.combine meth_params es in
      (* [Oct-6-2022] substitution should also include result |-> x in
         order to handle x := m(args) when m's frame includes result. *)
      let subst = match x with
        | None -> subst
        | Some x -> (Ast.Id "result" -: meth_result_ty, x) :: subst in
      let eff = subst_effect subst meth_effects in
      wr_to_x @ eff
    with Not_found -> wr_to_x


(* -------------------------------------------------------------------------- *)
(* Compute the boundary to be respected by each module                        *)
(* -------------------------------------------------------------------------- *)

(* resp_bnd E = bnd

   Where bnd is the collective boundary to be respected by non-call atomic
   commands and guards for conditionals and loops.  The collective boundary
   is simply the boundary of all imported modules.
*)
let resp_bnd curr_mdl = Boundary_info.imported_boundaries curr_mdl

(* FIXME: Repeated in locEq.ml *)
module BndSet = Set.Make (struct
    type t = effect_desc Annot.t
    let compare = compare
  end)

module EffSet = Set.Make (struct
    type t = effect_elt
    let compare = compare
  end)

let resp_bnd_call meth_map curr_mdl meth_name =
  let open BndSet in
  let open Boundary_info in
  let set = of_list in
  (* If m is a math function (not present in meth_map), then the boundary to
     be respected is empty. *)
  match M.find meth_name meth_map with
  | m ->
    let {meth_module; _} = m in
    let my_bnd = set (boundary curr_mdl) in
    let full_bnd = union my_bnd (set (imported_boundaries curr_mdl)) in
    let mdl_bnd = set (boundary meth_module) in
    let mdl_imported_bnd = set (imported_boundaries meth_module) in
    let mdl_resp_bnd = union mdl_imported_bnd mdl_bnd in
    let fin = diff full_bnd mdl_resp_bnd in
    elements fin
  | exception Not_found -> []


(* -------------------------------------------------------------------------- *)
(* Perform the encapsulation check                                            *)
(* -------------------------------------------------------------------------- *)

(* check_atomic_command curr_mdl ctbl ac = f

   If bnd % eff, where eff is the effect of atomic command ac and bnd is the
   collective boundary of imported modules, then f = None.  If bnd % eff
   cannot be determined statically, then f = Some f' where f' is a conjunction
   of disjointness formulas.

   If bnd % eff does not hold, Encap_check_fail is raised.
*)
let check_atomic_command meth_map curr_mdl ctbl ac =
  let eff = acom_effect meth_map ctbl ac in
  let eff = nub (wrs eff @ r2w eff)  in
  let bnd = match ac with
    | Call (_, m, _) -> resp_bnd_call meth_map curr_mdl m.node
    | _ -> resp_bnd curr_mdl in
  let bnd_eff = eff_of_bnd bnd in

  match separator_check bnd_eff eff with (* bnd_eff % eff *)
  | Separate -> None
  | Not_separate -> raise (Encap_check_fail (Ok ac))
  | Separate_if f ->
    if !encap_debug then begin
      Format.fprintf Format.err_formatter
        "Encap check assertion for %a: %a\n"
        Pretty.pp_atomic_command ac
        Pretty.pp_formula f;
      Format.pp_print_flush Format.err_formatter ()
    end;
    Some f

type read_eff_fail = {
    mdl_name: string;
    meth_name: string;
    source_name: string;
    exp_or_command: string;
  }

exception Read_var_failure of read_eff_fail
exception Read_img_failure of read_eff_fail

let rec simplify_subseteq_formula frm =
  match frm with
  | Fnot f' -> Fnot (simplify_subseteq_formula f')
  | Fconn (Conj, f1, f2) ->
     let f1' = simplify_subseteq_formula f1 in
     let f2' = simplify_subseteq_formula f2 in
     begin match f1', f2' with
     | Ftrue, h | h, Ftrue -> h
     | Ffalse, h | h, Ffalse -> Ffalse
     | f, f' when f = f' -> f
     | _, _ -> Fconn (Conj, f1', f2')
     end
  | Fconn (Disj, f1, f2) ->
     let f1' = simplify_subseteq_formula f1 in
     let f2' = simplify_subseteq_formula f2 in
     begin match f1', f2' with
     | Ftrue, h | h, Ftrue -> Ftrue
     | f, f' when f = f' -> f
     | _, _ -> Fconn (Disj, f1', f2')
     end
  | Fsubseteq ({node = Esingleton e}, {node = Esingleton e'}) ->
     Fexp (Ebinop (Equal, e, e') -: Tbool)
  | Fsubseteq ({node = Esingleton e}, g) -> Fmember (e, g)
  | Fsubseteq (g, {node = Esingleton e}) -> Fmember (e, g)
  | Fsubseteq (g, g') when g = g' -> Ftrue
  | _ -> frm

(* check_reads

   curr_mdl, meth_name -- which module and method we are looking at
   mrds -- reads of the method in curr_mdl with name meth_name
   source -- are we looking at an exp or command? a string; for error messages
   locals -- locals in method up to the exp or command we are looking at
   eff -- rds of exp or atomic command we are looking at
 *)
let check_reads curr_mdl meth_name mrds source locals eff =
  let mk_conj f1 f2 = Fconn (Conj, f1, f2) in
  let mk_rd_err s =
    let mdl_name = string_of_ident curr_mdl in
    let source_name = string_of_ident s.node in
    {mdl_name; meth_name; source_name; exp_or_command = source} in
  let alloc = Evar alloc_var -: Trgn in
  let alloc_init = Einit alloc -: Trgn in
  let fresh_refs = Ebinop (Diff, alloc, alloc_init) -: Trgn in
  let null_exp = Econst (Enull -: Tanyclass) -: Tanyclass in
  let sing_null = Esingleton null_exp -: Trgn in
  let rec ok_reads frms = function
    | [] -> foldr mk_conj Ftrue (FrmSet.elements frms)
    | {effect_desc = {node = Effvar x}} :: eff ->
       if contains_var mrds x || mem x.node (map (fun {node} -> node) locals)
       then ok_reads frms eff
       else raise (Read_var_failure (mk_rd_err x))
    | {effect_desc = {node = Effimg({node = Esingleton e}, f)}} :: eff -> begin
        match find_img_field mrds f with
        | None ->
           (* mrds does not contain G`f for any G -- assert freshness or null *)
           let e_fresh = Fnot (Fmember (e, alloc_init)) in
           let e_null = Fexp (Ebinop (Equal, e, null_exp) -: Tbool) in
           let frm = Fconn (Disj, e_fresh, e_null) in
           let frms = FrmSet.add frm frms in
           ok_reads frms eff
        | Some g' ->
           (* mrds contains g'`f -- e in (g' at INIT) or e is fresh *)
           let g'_init = (Einit g') -: g'.ty in
           let e_in_g' = Fmember (e, g'_init) in
           let e_fresh = Fnot (Fmember (e, alloc_init)) in
           let e_null = Fexp (Ebinop (Equal, e, null_exp) -: Tbool) in
           let frm = Fconn (Disj, e_in_g', Fconn (Disj, e_fresh, e_null)) in
           let frms = FrmSet.add frm frms in
           ok_reads frms eff
      end
    | {effect_desc = {node = Effimg(g, f)}} (* rd g`f *) :: eff -> begin
        match find_img_field mrds f with
        | None ->
           (* mrds does not contain rd G`f for any G -- assert freshness *)
           let g = Ebinop (Diff, g, sing_null) -: Trgn in
           let g_fresh = Fsubseteq (g, fresh_refs) in
           let frms = FrmSet.add g_fresh frms in
           ok_reads frms eff
        | Some g' ->
           (* reads of the method contain rd g'`f *)
           (* (g \ null) subset of ((g' at INIT) union (alloc \ s_alloc)) *)
           let g = Ebinop (Diff, g, sing_null) -: Trgn in
           let g'_init = (Einit g') -: g'.ty in
           let g'_and_fresh = Ebinop (Union, g'_init, fresh_refs) -: Trgn in
           let g_sub = Fsubseteq (g, g'_and_fresh) in
           let frm = simplify_subseteq_formula g_sub in
           let frms = FrmSet.add frm frms in
           ok_reads frms eff
      end
  in
  let frm = ok_reads FrmSet.empty eff in
  if frm = Ftrue then None else Some frm

let check_atomic_command_reads meth_map curr_mdl name ctbl mrds locals ac =
  let eff = acom_effect meth_map ctbl ac in
  let eff = Norm.normalize (nub (rds eff)) in
  let mrds = map (fun {effect_desc} -> effect_desc.node) (Norm.normalize mrds) in
  let src = pp_as_string Pretty.pp_atomic_command ac in
  check_reads curr_mdl name mrds src locals eff

let check_guard_reads curr_mdl meth_name mrds locals guard =
  let eff = Norm.normalize (ftpt_exp guard) in
  let src = pp_as_string Pretty.pp_exp guard in
  let mrds = map (fun {effect_desc} -> effect_desc.node) (Norm.normalize mrds) in
  check_reads curr_mdl meth_name mrds src locals eff

(* check_command curr_mdl ctbl mrds locals c = c'

   Checks all atomic commands and guards of conditionals and loops in c.  If
   none fail the encap check, then c' is c with (possibly) additional
   annotations, asserting disjointness of certain regions.  If these
   assertions hold, then transition steps c may take satisfy the encap
   condition.

   Can raise Encap_check_fail.

   24 May, 2021
   NEW: mrds is the reads of the method m in curr_mdl whose body is c.
        name is the name of the method.
        locals maintains a list of local variables in c
*)
let rec check_command meth_map curr_mdl name ctbl mrds locals c =
  match c with
  | Acommand ac ->
     let disjoint_assrt = check_atomic_command meth_map curr_mdl ctbl ac in
     let reads_assrt =
       check_atomic_command_reads meth_map curr_mdl name ctbl mrds locals ac in
     begin match disjoint_assrt, reads_assrt with
     | None, None -> Acommand ac
     | Some f, Some f' -> Seq (Assert f, Seq (Assert f', Acommand ac))
     | None, Some f | Some f, None -> Seq (Assert f, Acommand ac)
    end
  (* CHECK_AGAIN: FIXME: If global variable, part of a modules boundary, is
     shadowed by a local, then encap check fails *)
  | Vardecl (x, m, ty, c) ->
    let locals = x :: locals in
    let c = check_command meth_map curr_mdl name ctbl mrds locals c in
    Vardecl (x, m, ty, c)
  | Seq (c, c') ->
    let c = check_command meth_map curr_mdl name ctbl mrds locals c in
    let c' = check_command meth_map curr_mdl name ctbl mrds locals c' in
    Seq (c, c')
  | If (e, c, c') ->
    let c = check_command meth_map curr_mdl name ctbl mrds locals c in
    let c' = check_command meth_map curr_mdl name ctbl mrds locals c' in
    let disjoint_assrt = check_guard curr_mdl e in
    let reads_assrt = check_guard_reads curr_mdl name mrds locals e in
    begin match disjoint_assrt, reads_assrt with
    | None, None -> If (e, c, c')
    | Some f, Some f' -> Seq (Assert f, Seq (Assert f', If (e, c, c')))
    | None, Some f | Some f, None -> Seq (Assert f, If (e, c, c'))
    end
  | While (e, inv, c) ->
    let c = check_command meth_map curr_mdl name ctbl mrds locals c in
    let disjoint_assrt = check_guard curr_mdl e in
    let reads_assrt = check_guard_reads curr_mdl name mrds locals e in
    begin match disjoint_assrt, reads_assrt with
    | None, None -> While (e, inv, c)
    | Some f, Some f' -> Seq (Assert f, Seq (Assert f', While (e, inv, c)))
    | None, Some f | Some f, None -> Seq (Assert f, While (e, inv, c))
    end
  | Assume f | Assert f -> c

(* Check the guard of a conditional or loop *)
and check_guard curr_mdl e =
  let eff = r2w (ftpt_exp e) in
  let bnd_eff = eff_of_bnd (resp_bnd curr_mdl) in
  match separator_check bnd_eff eff with
  | Separate -> None
  | Not_separate -> raise (Encap_check_fail (Error e))
  | Separate_if f -> Some f

(* Perform encap check on a command and rewrite command so that ; is
   associated to the right. *)
let process_command meth_map curr_mdl name ctbl mrds res c =
  (* list of locals initially includes result *)
  reassoc_command (check_command meth_map curr_mdl name ctbl mrds [res] c)

let process_method_def meth_map curr_mdl ctbl mdef =
  let Method (mdecl, com) = mdef in
  let name = string_of_ident mdecl.meth_name.node in
  let frame = spec_effects mdecl.meth_spec in
  let rds = rds frame in
  let res = Ast.Id "result" -: mdecl.result_ty in
  match com with
  | None -> Method (mdecl, None)
  | Some c ->
     let c' = process_command meth_map curr_mdl name ctbl rds res c in
     Method (mdecl, Some c')

(* Process all method definitions in a module *)
let ec_module meth_map curr_mdl ctbl m =
  let f elt elts = match elt with
    | Mdl_mdef mdef ->
      Mdl_mdef (process_method_def meth_map curr_mdl ctbl mdef) :: elts
    | _ -> elt :: elts in
  {m with mdl_elts = List.fold_right f m.mdl_elts []}


(* -------------------------------------------------------------------------- *)
(* Driver                                                                     *)
(* -------------------------------------------------------------------------- *)

(* Process all modules in penv *)
let run (ctbl, penv) : penv =
  if !do_encap_check then begin
    let meth_map = meth_map_of_penv penv in
    let process name mdl env = match mdl with
      | Unary_module m ->
        let curr_mdl = m.mdl_name in
        let m' = ec_module meth_map curr_mdl ctbl m in
        M.add name (Unary_module m') env
      | _ -> M.add name mdl env in
    M.fold process penv M.empty
  end else penv

let run_maybe_exit (ctbl, penv) : penv =
  if !do_encap_check then begin
    try run (ctbl, penv) with
    | Encap_check_fail (Ok ac) ->
      let ac = pp_as_string Pretty.pp_atomic_command ac in
      Printf.fprintf stderr "Error: Encap check failed on command %s\n" ac;
      exit 2
    | Encap_check_fail (Error e) ->
      let e = pp_as_string Pretty.pp_exp e in
      Printf.fprintf stderr "Error: Encap check failed on expression %s\n" e;
      exit 2
    | Read_var_failure {mdl_name; meth_name; source_name; exp_or_command} ->
      Printf.fprintf stderr
        "Error: Expected %s::%s to read variable %s (see: %s)\n"
        mdl_name meth_name source_name exp_or_command;
      exit 2
    | Read_img_failure {mdl_name; meth_name; source_name; exp_or_command} ->
      Printf.fprintf stderr
        "Error: Expected %s::%s to read field %s (see: %s)\n"
        mdl_name meth_name source_name exp_or_command;
      exit 2
  end else penv
