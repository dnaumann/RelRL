(** resolve_datagroups.mli -- resolve (expand) datagroups *)

open Astutil
open Annot
open Lib

exception Resolve_datagroups_exn of string

let all_fields ctbl =
  let extract {field_name; field_ty; _} =
    assert (field_name.ty = field_ty);
    (field_name.node -: field_ty) in
  map extract (Ctbl.known_fields ctbl)

let is_datagroup {node; ty} = (node = Ast.Id "any") && (ty = Tdatagroup)

let no_datagroups effs =
  forall (fun {effect_desc;_} -> match effect_desc.node with
      | Effimg (_, f) -> not (is_datagroup f)
      | _ -> true
    ) effs

let is_resolved eff = no_datagroups eff

let resolve_effect' fields es =
  let resolve k t g f =
    {effect_kind = k; effect_desc = Effimg (g, f) -: t} in
  let walk ({effect_kind=k; effect_desc=eff} as e) =
    match eff.node with
    | Effimg (g, f) when is_datagroup f -> map (resolve k eff.ty g) fields
    | _ -> [e] in
  let res = concat_map walk es in
  assert (no_datagroups res);
  res

let resolve_effect ctbl eff = resolve_effect' (all_fields ctbl) eff

let resolve_boundary fields (bnd: boundary_decl) : boundary_decl =
  let resolve = function
    | {node = Effimg (g, f); ty } when is_datagroup f ->
      map (fun f' -> Effimg (g, f') -: ty) fields
    | e -> [e] in
  concat_map resolve bnd

let resolve_spec fields spec : spec =
  let rec walk = function
    | [] -> []
    | Effects es :: ss -> Effects (resolve_effect' fields es) :: walk ss
    | s :: ss -> s :: walk ss in
  walk spec

let rec resolve_command fields com : command =
  let ( ~! ) = resolve_command fields in
  match com with
  | Assume f -> Assume f
  | Assert f -> Assert f
  | Acommand ac -> Acommand ac
  | Vardecl (x, m, t, c) -> Vardecl (x, m, t, ~! c)
  | Seq (c1, c2) -> Seq (~! c1, ~! c2)
  | If (e, c1, c2) -> If  (e, ~! c1, ~! c2)
  | While (e, {winvariants; wframe; wvariant}, c) ->
    let wframe = resolve_effect' fields wframe in
    While (e, {winvariants; wframe; wvariant}, ~! c)

let resolve_command_opt fields = function
  | None -> None
  | Some c -> Some (resolve_command fields c)

let rec resolve_bicommand fields bicom : bicommand =
  let ( ~! ) = resolve_bicommand fields in
  match bicom with
  | Bihavoc_right (x, rf) -> Bihavoc_right (x, rf)
  | Bisplit (c1, c2) ->
    Bisplit (resolve_command fields c1, resolve_command fields c2)
  | Bisync ac -> Bisync ac
  | Bivardecl (x, x', cc) -> Bivardecl (x, x', ~! cc)
  | Biseq (cc1, cc2) -> Biseq (~! cc1, ~! cc2)
  | Biif (g, g', cc, dd) -> Biif (g, g', ~! cc, ~! dd)
  | Biif4 (g, g', branches) -> Biif4 (g, g', map_fourwayif (~!) branches)
  | Biwhile (e, e', ag, {biwinvariants; biwframe; biwvariant}, cc) ->
    let biwframe = map_pair (resolve_effect' fields) biwframe in
    Biwhile (e, e', ag, {biwinvariants; biwframe; biwvariant}, ~! cc)
  | Biassume rf -> Biassume rf
  | Biassert rf -> Biassert rf
  | Biupdate (x, x') -> Biupdate (x, x')

let resolve_bicommand_opt fields = function
  | None -> None
  | Some cc -> Some (resolve_bicommand fields cc)

let resolve_meth_decl fields mdecl : meth_decl =
  let meth_spec = resolve_spec fields mdecl.meth_spec in
  { mdecl with meth_spec }

let resolve_meth_def fields mdef : meth_def =
  let Method (mdecl, com) = mdef in
  let mdecl' = resolve_meth_decl fields mdecl in
  Method (mdecl', resolve_command_opt fields com)

let resolve_bispec fields bispec : bispec =
  let rec walk = function
    | [] -> []
    | Bieffects (es1, es2) :: ss ->
      let es1' = resolve_effect' fields es1 in
      let es2' = resolve_effect' fields es2 in
      Bieffects (es1', es2') :: walk ss
    | s :: ss -> s :: walk ss in
  walk bispec

let resolve_bimeth_decl fields bimdecl : bimeth_decl =
  let bimeth_spec = resolve_bispec fields bimdecl.bimeth_spec in
  { bimdecl with bimeth_spec }

let resolve_bimeth_def fields bimdef : bimeth_def =
  let Bimethod (bimdecl, cc) = bimdef in
  let bimdecl' = resolve_bimeth_decl fields bimdecl in
  Bimethod (bimdecl', resolve_bicommand_opt fields cc)

let resolve_interface fields intr : interface_def =
  let aux = function
    | Intr_mdecl mdecl -> Intr_mdecl (resolve_meth_decl fields mdecl)
    | Intr_boundary bnd -> Intr_boundary (resolve_boundary fields bnd)
    | e -> e in
  let elts = foldr (fun e es -> aux e :: es) [] intr.intr_elts in
  { intr with intr_elts = elts }

let resolve_module fields mdl : module_def =
  let aux = function
    | Mdl_mdef mdef -> Mdl_mdef (resolve_meth_def fields mdef)
    | e -> e in
  let elts = foldr (fun e es -> aux e :: es) [] mdl.mdl_elts in
  { mdl with mdl_elts = elts }

let resolve_bimodule fields bimdl : bimodule_def =
  let aux = function
    | Bimdl_mdef mdef -> Bimdl_mdef (resolve_bimeth_def fields mdef)
    | e -> e in
  let elts = foldr (fun e es -> aux e :: es) [] bimdl.bimdl_elts in
  { bimdl with bimdl_elts = elts }

let resolve (ctbl, penv) =
  let open M in
  let fields = all_fields ctbl in
  fold (fun k v ps ->
      match v with
      | Unary_interface intr ->
        add k (Unary_interface (resolve_interface fields intr)) ps
      | Unary_module mdl ->
        add k (Unary_module (resolve_module fields mdl)) ps
      | Relation_module bimdl ->
        add k (Relation_module (resolve_bimodule fields bimdl)) ps
    ) penv empty
