(* astutil.ml -- functions on syntax trees and other utilities *)

open Ast

module Ident : Map.OrderedType with type t = ident =
struct
  type t = ident
  let compare = compare
end

module M = Map.Make (Ident)
module S = Set.Make (Ident)

let mk_node (loc: loc) (elt: 'a) : 'a node = {elt; loc}

let get_elts (ls: 'a node list) : 'a list =
  List.map (fun {elt;_} -> elt) ls

let string_of_ident = function
  | Id id -> id
  | Qualid (id, ids) -> String.concat "::" (id :: ids)

let rec string_of_ty ty =
  match ty.elt with
  | Tctor (name, tys) ->
    let others = List.map string_of_ty tys in
    String.concat " " (others @ [string_of_ident name])

let string_of_modifier = function
  | Public -> "public"
  | Ghost -> "ghost"
  | Modscope -> "modscope"

let string_of_loc (loc: loc) =
  let (lpos,rpos) = loc.loc_range in
  Printf.sprintf "%s:%d:%d-%d"
    loc.loc_fname loc.loc_line lpos rpos

let is_left_value (v: value_in_state node) =
  match v.elt with
  | Left _ -> true
  | _ -> false

let is_right_value (v: value_in_state node) =
  match v.elt with
  | Right _ -> true
  | _ -> false

let get_program_elt_name (p: program_elt) : ident =
  match p with
  | Unr_intr i -> i.elt.intr_name
  | Unr_mdl  m -> m.elt.mdl_name
  | Rel_mdl bm -> bm.elt.bimdl_name

let the_main_interface = {intr_name = Id "MAIN"; intr_elts = []}

let is_relation_module (p: program_elt node) : bool =
  match p.elt with
  | Rel_mdl _ -> true
  | _ -> false

let interface_methods (idef: interface_def node) : meth_decl node list =
  List.filter_map (function
      | Intr_mdecl m -> Some m
      | _ -> None
    ) @@ get_elts idef.elt.intr_elts

let interface_classes (idef: interface_def node) : class_decl node list =
  List.filter_map (function
      | Intr_cdecl c -> Some c
      | _ -> None
    ) @@ get_elts idef.elt.intr_elts

let interface_datagroups (idef: interface_def node) : ident list =
  Lib.concat_filter_map (function
      | Intr_datagroup id -> Some id
      | _ -> None
    ) @@ get_elts idef.elt.intr_elts

let interface_predicates (idef: interface_def node) : named_formula node list =
  List.filter_map (function
      | Intr_formula nf when nf.elt.kind = `Predicate -> Some nf
      | _ -> None
    ) @@ get_elts idef.elt.intr_elts

let interface_inductives (idef: interface_def node) : inductive_predicate node list =
  List.filter_map (function
      | Intr_inductive ind -> Some ind
      | _ -> None
    ) @@ get_elts idef.elt.intr_elts

let interface_imports (idef: interface_def node) : import_directive node list =
  List.filter_map (function
      | Intr_import i -> Some i
      | _ -> None
    ) @@ get_elts idef.elt.intr_elts

let module_methods (mdef: module_def node) : meth_def node list =
  List.filter_map (function
      | Mdl_mdef m -> Some m
      | _ -> None
    ) @@ get_elts mdef.elt.mdl_elts

let module_classes (mdef: module_def node) : class_def node list =
  List.filter_map (function
      | Mdl_cdef c -> Some c
      | _ -> None
    ) @@ get_elts mdef.elt.mdl_elts

let module_datagroup_names (mdef: module_def node) : ident list =
  List.filter_map (function
      | Mdl_datagroup (id, _) -> Some id
      | _ -> None
    ) @@ get_elts mdef.elt.mdl_elts

let module_predicates (mdef: module_def node) : named_formula node list =
  List.filter_map (function
      | Mdl_formula nf when nf.elt.kind = `Predicate -> Some nf
      | _ -> None
    ) @@ get_elts mdef.elt.mdl_elts

let module_inductives (mdef: module_def node) : inductive_predicate node list =
  List.filter_map (function
      | Mdl_inductive ind -> Some ind
      | _ -> None
    ) @@ get_elts mdef.elt.mdl_elts

let module_imports (mdef: module_def node) : import_directive node list =
  List.filter_map (function
      | Mdl_import i -> Some i
      | _ -> None
    ) @@ get_elts mdef.elt.mdl_elts

let bimodule_imports (bimdef: bimodule_def node) : import_directive node list =
  List.filter_map (function Bimdl_import i -> Some i | _ -> None)
  @@ get_elts bimdef.elt.bimdl_elts


(* -------------------------------------------------------------------------- *)
(* Equality modulo location info                                              *)
(* -------------------------------------------------------------------------- *)

let rec equal_ty (t: ty node) (t': ty node) =
  let open List in
  match t.elt, t'.elt with
  | Tctor (k, tys), Tctor (k', tys') ->
    k = k'
    && length tys = length tys'
    && for_all2 equal_ty tys tys'

let rec equal_exp (e: exp node) (e': exp node) =
  let open List in
  match e.elt, e'.elt with
  | Econst {elt=c; _}, Econst {elt=c'; _} -> c = c'
  | Evar id, Evar id' -> id = id'
  | Ebinop (op, e1, e2), Ebinop (op', e1', e2') ->
    op = op' && equal_exp e1 e1' && equal_exp e2 e2'
  | Eunrop (op, e), Eunrop (op', e') ->
    op = op' && equal_exp e e'
  | Esingleton e, Esingleton e' -> equal_exp e e'
  | Esubrgn (e, k), Esubrgn (e', k') -> equal_exp e e' && k = k'
  | Eimage (g, f), Eimage (g', f') -> equal_exp g g' && f = f'
  | Ecall (fn, args), Ecall (fn', args') ->
    fn = fn'
    && length args = length args'
    && for_all2 equal_exp args args'
  | _, _ -> false

let equal_exp_opt (e: exp node option) (e': exp node option) =
  match e, e' with
  | Some e, Some e' -> equal_exp e e'
  | _, _ -> e = e'

let equal_let_bound_value (lb: let_bound_value node) lb' =
  match lb.elt, lb'.elt with
  | Lloc (y, f), Lloc (y', f') -> y = y' && f = f'
  | Larr (a, idx), Larr (a', idx') -> a = a' && equal_exp idx idx'
  | Lexp e, Lexp e' -> equal_exp e e'
  | _, _ -> false

let equal_let_bind (lb: let_bind) (lb': let_bind) =
  equal_let_bound_value lb.value lb'.value && lb.is_old = lb'.is_old

let equal_quantifier_bindings (qbs: quantifier_bindings) qbs' =
  let rec walk qbs qbs' =
    match qbs, qbs' with
    | [], [] -> true
    | q :: qbs, q' :: qbs' ->
      q.name = q'.name
      && equal_ty q.ty q'.ty
      && equal_exp_opt q.in_rgn q'.in_rgn
      && q.is_non_null = q'.is_non_null
      && walk qbs qbs'
    | _, _ -> false in
  List.length qbs = List.length qbs' && walk qbs qbs'

let rec equal_formula (f: formula node) (f': formula node) =
  match f.elt, f'.elt with
  | Ftrue, Ftrue | Ffalse, Ffalse -> true
  | Fexp e, Fexp e' -> equal_exp e e'
  | Fnot f, Fnot f' -> equal_formula f f'
  | Fpointsto (y, f, e), Fpointsto (y', f', e') ->
    y = y' && f = f' && equal_exp e e'
  | Farray_pointsto (a, idx, e), Farray_pointsto (a', idx', e') ->
    a = a' && equal_exp idx idx' && equal_exp e e'
  | Fsubseteq (g1, g2), Fsubseteq (g1', g2') ->
    equal_exp g1 g1' && equal_exp g2 g2'
  | Fmember (x, g), Fmember (x', g') ->
    equal_exp x x' && equal_exp g g'
  | Flet (x, tyopt, value, frm), Flet (x', tyopt', value', frm') ->
    x = x' && equal_let_bind value value'
    && begin match tyopt, tyopt' with
      | Some ty, Some ty' -> equal_ty ty ty'
      | None, None -> true
      | _, _ -> false
    end
    && equal_formula frm frm'
  | Fconn (c, f1, f2), Fconn (c', f1', f2') ->
    c = c' && equal_formula f1 f1' && equal_formula f2 f2'
  | Fquant (q, qbs, frm), Fquant (q', qbs', frm') ->
    q = q' && equal_quantifier_bindings qbs qbs' && equal_formula frm frm'
  | Fold (e, value), Fold (e', value') ->
    equal_exp e e' && equal_let_bound_value value value'
  | Ftype (e, ty), Ftype (e', ty') ->
    equal_exp e e' && ty = ty'
  | _, _ -> false

let equal_atomic_command (ac: atomic_command node) ac' =
  match ac.elt, ac'.elt with
  | Skip, Skip -> true
  | Havoc x, Havoc x' -> x = x'
  | Assign (x, e), Assign (x', e') -> x = x' && equal_exp e e'
  | New_class (x, k), New_class (x', k') -> x = x' && k = k'
  | New_array (x, ty, sz), New_array (x', ty', sz') ->
    x = x' && ty = ty' && equal_exp sz sz'
  | Field_deref (y, x, f), Field_deref (y', x', f') ->
    y = y' && x = x' && f = f'
  | Field_update (x, f, e), Field_update (x', f', e') ->
    x = x' && f = f' && equal_exp e e'
  | Array_access (x, a, i), Array_access (x', a', i') ->
    x = x' && a = a' && equal_exp i i'
  | Array_update (a, i, e), Array_update (a', i', e') ->
    a = a' && equal_exp i i' && equal_exp e e'
  | Call (xopt, m, args), Call (xopt', m', args') ->
    xopt = xopt' && m = m'
    && List.length args = List.length args'
    && List.for_all2 (=) args args'
  | _, _ -> false

let rec equal_command (c: command node) (c': command node) =
  match c.elt, c'.elt with
  | Acommand ac, Acommand ac' -> equal_atomic_command ac ac'
  | Vardecl (id, mopt, ty, c), Vardecl (id', mopt', ty', c') ->
    id = id' && mopt = mopt' && equal_ty ty ty' && equal_command c c'
  | Seq (c1, c2), Seq (c1', c2') ->
    equal_command c1 c1' && equal_command c2 c2'
  | If (e, c1, c2), If (e', c1', c2') ->
    equal_exp e e' && equal_command c1 c1' && equal_command c2 c2'
  | While (e, _, c), While (e', _, c') -> (* FIXME: does not check spec *)
    equal_exp e e' && equal_command c c'
  | Assume f, Assume f' | Assert f, Assert f' ->
    equal_formula f f'
  | _, _ -> false

let equal_param_info (p: meth_param_info) (p': meth_param_info) =
  equal_ty p.param_ty p'.param_ty
  && p.param_name = p'.param_name
  && p.param_modifier = p'.param_modifier
  && p.is_non_null = p'.is_non_null

let equal_field (f: field_decl node) (f': field_decl node) : bool =
  f.elt.field_name = f'.elt.field_name
  && equal_ty f.elt.field_ty f'.elt.field_ty
  && f.elt.attribute = f'.elt.attribute

(* -------------------------------------------------------------------------- *)
(* Qualify names                                                              *)
(* -------------------------------------------------------------------------- *)

let qualify_ident (id: ident) (qual: string option) : ident =
  match qual, id with
  | None, _ -> id
  | Some qual, Id name -> Qualid (qual, [name])
  | Some qual, Qualid (prefix, name) -> Qualid (qual, prefix :: name)

let rec qualify_ty (ty: ty node) (qual: string) : ty node =
  match ty.elt with
  | Tctor(Id "int", []) | Tctor(Id "bool", [])
  | Tctor(Id "rgn", []) | Tctor(Id "unit", []) -> ty
  | Tctor(Id "array", [base_ty]) ->
    {elt = Tctor(Id "array", [qualify_ty base_ty qual]); loc = ty.loc}
  | Tctor(tyname, ts) ->
    let tyname = qualify_ident tyname (Some qual) in
    let ts = List.map (fun t -> qualify_ty t qual) ts in
    {elt = Tctor(tyname, ts); loc = ty.loc}
