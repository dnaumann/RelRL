(** typing.ml -- type checking and wf conditions *)

open Ast
open Astutil
open Lib
open Result
open Result.Monad_syntax

module T = Annot
type ity = T.ity
let ( -: ) = T.( -: )

let tc_debug = ref false
let all_exists_mode = ref false

(* -------------------------------------------------------------------------- *)
(* Typing environments                                                        *)
(* -------------------------------------------------------------------------- *)

type tenv = {
  ctxt: ity M.t;
  ctbl: Ctbl.t;
  grps: (ident * ident list) list; (* DEPRECATED: to be removed *)
  exts: ident list;          (* known extern types *)
}

let initial_tenv = {
  ctxt = M.add (Id "alloc") T.Trgn M.empty;
  ctbl = Ctbl.empty;
  grps = [];
  exts = []
}

type bi_tenv = {
  left_tenv: tenv;
  right_tenv: tenv;
  bipreds: bipred_params M.t;
}

and bipred_params = ity list * ity list

let initial_bi_tenv = {
  left_tenv  = initial_tenv;
  right_tenv = initial_tenv;
  bipreds    = M.empty;
}

let add_to_ctxt env id ty = { env with ctxt = M.add id ty env.ctxt }

(* DEBUG -- to remove *)
let show_tenv env =
  let show_bindings bindings =
    List.iter (fun (k,v) ->
        Printf.printf "%s --> %s\n" (string_of_ident k) (T.string_of_ity v)
      ) bindings in
  Ctbl.debug_print_ctbl stdout env.ctbl;
  show_bindings (M.bindings env.ctxt);
  List.iter (fun (id, contains) ->
      Printf.printf "%s contains { %s }\n" (string_of_ident id)
        (String.concat ", " @@ List.map string_of_ident contains)
    ) env.grps;
  List.iter (fun id ->
      Printf.printf "extern type %s\n" (string_of_ident id)
    ) env.exts

let is_array_ty = function
  | T.Tmath (Id "array", ty) -> Option.is_some ty
  | _ -> false

let is_class_ty = function T.Tclass _ | Tanyclass -> true | _ -> false

let is_math_ty = function T.Tmath _ -> true | _ -> false

let is_array_field = function   (* DEPRECATED *)
  | Id name -> name = "length" || name = "slots"
  | Qualid _ -> false

(* let is_datagroup env f = List.mem f (List.map fst env.grps) *)
let is_datagroup f = (f = Id "any")

let math_array_base_ty = function
  | T.Tmath (Id "array", Some ty) -> ty
  | _ -> invalid_arg "array_base_ty"

let binop_ty (b: binop) : ity * ity * ity =
  match b with
  | Plus  | Minus | Mult | Div | Mod -> Tint, Tint, Tint
  | Leq   | Lt    | Geq  | Gt  -> Tint, Tint, Tbool
  | Union | Inter | Diff       -> Trgn, Trgn, Trgn
  | And   | Or                 -> Tbool, Tbool, Tbool
  | Equal | Nequal -> invalid_arg "binop_ty"

let unrop_ty (u: unrop) : ity * ity =
  match u with
  | Uminus -> Tint, Tint
  | Not    -> Tbool, Tbool

let rec is_known_type env ty =
  match ty with
  | Tctor(Id "int", []) | Tctor(Id "bool", [])
  | Tctor(Id "rgn", []) | Tctor(Id "unit", []) -> true
  | Tctor(name, []) ->
    Ctbl.class_exists env.ctbl ~classname:name || List.mem name env.exts
  | Tctor(Id "array", [base_ty]) -> is_known_type env base_ty.elt
  | _ -> false

let rec ity_of_ty env = function
  | Tctor(Id "int", []) -> T.Tint
  | Tctor(Id "rgn", []) -> T.Trgn
  | Tctor(Id "bool", []) -> T.Tbool
  | Tctor(Id "unit", []) -> T.Tunit
  | Tctor(cname, []) ->
    if Ctbl.class_exists env.ctbl ~classname:cname then T.Tclass cname else
    if List.mem cname env.exts then T.Tmath (cname, None)
    else invalid_arg ("ity_of_ty: " ^ string_of_ident cname)
  | Tctor(Id "array", [ty]) -> T.Tmath (Id "array", Some (ity_of_ty env ty.elt))
  | Tctor(ename, [t]) as ty ->
    if List.mem ename env.exts then
      let inner = Some (ity_of_ty env t.elt) in
      T.Tmath (ename, inner)
    else invalid_arg ("ity_of_ty: " ^ string_of_ty (no_loc ty))
  | ty -> invalid_arg ("ity_of_ty: " ^ string_of_ty (no_loc ty))

let ity_of_ty_opt env = Option.map (ity_of_ty env)

let ity_of_meth_decl (env: tenv) (mdecl: meth_decl) =
  let ret = ity_of_ty env mdecl.result_ty.elt in
  let params = List.map (fun e -> e.param_ty.elt) mdecl.params in
  let params = List.map (ity_of_ty env) params in
  T.Tmeth {params; ret}

let ity_of_named_formula (env: tenv) (nf: named_formula) =
  match nf.kind with
  | `Axiom | `Lemma -> T.Tprop
  | `Predicate ->
    let params = List.map (fun (_,t) -> ity_of_ty env t.elt) nf.params in
    Tfunc { params; ret = Tprop }

let ity_of_inductive_predicate (env: tenv) (ind: inductive_predicate) =
  let params = List.map (fun (_,t) -> ity_of_ty env t.elt) ind.ind_params in
  T.Tfunc { params; ret = Tprop }

(* Create a copy of env, prefixing all identifiers and types with qual *)
let qualify_tenv (env: tenv) (qual: string) : tenv =
  let {ctxt; ctbl; grps; exts} = env in
  let ctbl = Ctbl.qualify_ctbl ctbl qual in
  let ctxt =
    M.fold (fun id ity new_ctxt ->
        M.add
          (qualify_ident id (Some qual))
          (T.qualify_ity ity qual)
          new_ctxt
      ) ctxt M.empty in
  let grps =
    List.map (fun (e,ls) ->
        (qualify_ident e (Some qual),
         List.map (fun e -> qualify_ident e (Some qual)) ls)
      ) env.grps in
  let exts =
    List.map (fun e -> qualify_ident e (Some qual)) env.exts in
  { ctbl; ctxt; grps; exts }

let tenv_union (env1: tenv) (env2: tenv) : tenv =
  let ctxt = M.union (fun k v1 v2 -> Some v1) env1.ctxt env2.ctxt in
  let ctbl = Ctbl.union env1.ctbl env2.ctbl in
  let grps = env1.grps @ env2.grps in
  let exts = env1.exts @ env2.exts in
  { ctxt; ctbl; grps; exts }

let tenv_union_qualified (env1: tenv) (env2: tenv) (qual: ident option) : tenv =
  match qual with
  | Some (Id qual) -> tenv_union env1 (qualify_tenv env2 qual)
  | Some (Qualid _) ->
    (* This function is used in a context where we want to process
       "import Mod as M".  The parser does not allow M to be a
       qualified identifier.  Hence, this assert false is justified. *)
    assert false
  | None -> tenv_union env1 env2

let bi_tenv_union (env1: bi_tenv) (env2: bi_tenv) : bi_tenv =
  let bipreds = M.union (fun _ v _ -> Some v) env1.bipreds env2.bipreds in
  let left_tenv = tenv_union env1.left_tenv env2.left_tenv in
  let right_tenv = tenv_union env1.right_tenv env2.right_tenv in
  { left_tenv; right_tenv; bipreds }


(* -------------------------------------------------------------------------- *)
(* Annotated syntax                                                           *)
(* -------------------------------------------------------------------------- *)

(* Smart constructors -- handle annotating expressions with their result type *)

let mk_binop op e1 e2 =
  let res_ty =
    match op with
    | Equal | Nequal -> T.Tbool
    | _ -> let _, _, res_ty = binop_ty op in res_ty in
  T.Ebinop (op, e1, e2) -: res_ty

let mk_unrop op e =
  let _, res_ty = unrop_ty op in
  T.Eunrop (op, e) -: res_ty

let mk_singleton e = T.Esingleton e -: Trgn

let mk_var x ty = T.Evar (x -: ty) -: ty

(* mk_image G f t = r

   Invariant:
   If t = Type(f) then r = (G`(f : t) : rgn) is a well-typed
   annotated expression.
*)
let mk_image g f f_ty = T.Eimage (g, f -: f_ty) -: Trgn

(* mk_const ce = (e : ce.ty)

   Invariant:
   If ce is a well-typed annotated const_exp, then e = Econst ce is a
   well-typed annotated exp.
*)
let mk_const ce = T.Econst ce -: ce.ty


(* -------------------------------------------------------------------------- *)
(* Program environment that keeps track of typing status                      *)
(* -------------------------------------------------------------------------- *)

(* If a program_elt is Typed, then it need not be checked again.  Further,
   its environment containing any global symbols it exports is tracked.

   TODO: FIXME: The unannotated AST is kept around because some WF
   checks were written to work with parse trees instead of annotated
   trees.  It can be dropped after updating those functions.
*)

type tenviron =
  | Unary of tenv
  | Relational of bi_tenv

type tprogram_elt =
  | Typed of Ast.program_elt * T.program_elt * tenviron
  | Untyped of Ast.program_elt

type tpenv = tprogram_elt M.t

let empty_tpenv : tpenv = M.empty

let update_tpenv_unary (penv: tpenv) name orig_prog annot_prog tenv : tpenv =
  let value _ = Some (Typed (orig_prog, annot_prog, Unary tenv)) in
  M.update name value penv

let update_tpenv_relational (penv: tpenv) name orig annot bi_tenv : tpenv =
  let value _ = Some (Typed (orig, annot, Relational bi_tenv)) in
  M.update name value penv

let to_program_map (env: tpenv) : T.program_elt M.t =
  M.map (function
      | Typed (_, e, _) -> e
      | Untyped _ -> invalid_arg "to_program_map: untyped program_elt"
    ) env


(* -------------------------------------------------------------------------- *)
(* Type checking and Well-formedness conditions (unary code)                  *)
(* -------------------------------------------------------------------------- *)

let (>>) m k = let* _ = m in k

type errmsg = {msg: string; errloc: loc}

let mk_errmsg msg errloc = {msg; errloc}

let string_of_errmsg {msg; errloc} =
  Printf.sprintf "Type error: %s: %s" (string_of_loc errloc) msg

let error_out msg errloc = error (string_of_errmsg (mk_errmsg msg errloc))

let expected_msg s1 s2 =
  Printf.sprintf
    "This expression has type %s but an expression was expected of type %s"
    s1 s2

let got_but_expected got expected =
  expected_msg (T.string_of_ity got) (T.string_of_ity expected)

(* expect_tys ts = E

   Invariant:
   Let (loc, ty, ty') be in ts.  E is ok () iff equiv_ty ty ty';
   otherwise E is an error message with location loc.
*)
let rec expect_tys (expects: (loc * ity * ity) list)
  : (unit, string) result =
  match expects with
  | [] -> ok ()
  | (loc, got, expected) :: expects ->
    if T.equiv_ity got expected
    then expect_tys expects
    else let msg = got_but_expected got expected in
      error_out msg loc

let expect_ty loc t1 t2 = expect_tys [loc, t1, t2]

(* expect_ty_pred loc ty P msg = E

   Invariant:
   If (P ty) then E is ok (); otherwise E is an error message with
   location loc.  msg is a string representing the expected value of
   ty.
*)
let expect_ty_pred loc got pred expected : (unit, string) result =
  if pred got
  then ok ()
  else error_out (expected_msg (T.string_of_ity got) expected) loc

let expected_n_args loc fn n got =
  let msg =
    Printf.sprintf
      "%s expects %d argument(s) but is applied to %d argument(s)" fn n got in
  error_out msg loc

let ensure_class_exists env loc k =
  let cname = string_of_ident k in
  if Ctbl.class_exists env.ctbl ~classname:k
  then ok ()
  else error_out (Printf.sprintf "Unknown class %s" cname) loc

let ensure_type_is_known env ty =
  let tyname = string_of_ty ty in
  if is_known_type env ty.elt
  then ok ()
  else error_out (Printf.sprintf "Unknown type %s" tyname) ty.loc

(* find_in_ctxt G x loc = t

   Invariant:
   If (x : T) in G, then t = ok T; otherwise t is an error message
   with location loc.
*)
let find_in_ctxt env id loc =
  match M.find id env.ctxt with
  | res -> ok res
  | exception Not_found ->
    error_out (Printf.sprintf "Unknown identifier %s" (string_of_ident id)) loc

(* Why3 keywords that are not also source language keywords.  To keep
   things simple, source programs cannot use these as variables and
   field names.
*)
let disallowed_ident_names = [
  "val"; "returns"; "inductive"; "coinductive";
  "by"; "so"; "match"; "with"; "fun"; "for"; "to"; "downto";
  "label"; "raises"; "raise"; "exception"; "diverges"; "variant";
  "goal"; "use"; "clone"; "scope"; "constant"; "function";
  "type"; "range"; "float"; "check";
]

let wf_ident loc id : (unit, string) result =
  let get_name = function
    | Id name -> ok name
    | Qualid (_, _) as id ->
      error_out (
        Printf.sprintf
          "Qualified identifiers (such as %s) not supported in \
           this version\n"
          (string_of_ident id)
      ) loc in
  let check_prefix = function
    | Id name ->
      if String.starts_with ~prefix:T.reserved_id_prefix name
      then error_out (
          Printf.sprintf
            "%s is a reserved identifier prefix and cannot be \
             used in source programs\n"
            T.reserved_id_prefix
        ) loc
      else ok ()
    | Qualid _ -> assert false in
  let* name = get_name id in
  let* () = check_prefix id in
  if not (List.mem name disallowed_ident_names)
  then ok ()
  else error_out
      (Printf.sprintf "Identifier %s is restricted and cannot be \
                       used in source programs."
         (string_of_ident id))
      loc

let wf_ident_opt loc id : (unit, string) result =
  match id with
  | Some id -> wf_ident loc id
  | None -> ok ()

(* tc_heap_location G loc y f = J

   Invariant:
   If G |- y : K and f in Fields(K)
   then J = ok ((y : K).(f : t) : t, t) where t = FieldType(f)
*)
let tc_heap_location env loc y f
  : ((ident T.t * ident T.t) T.t * ity, string) result =
  let open Ctbl in
  let f_str = string_of_ident f in
  let y_str = string_of_ident y in
  let* y_ty = find_in_ctxt env y loc in
  match y_ty with
  | Tclass cname when class_exists env.ctbl ~classname:cname ->
    begin match field_type env.ctbl ~field:f with
      | Some f_ty when List.mem f (field_names env.ctbl ~classname:cname) ->
        ok ((y -: y_ty, f -: f_ty) -: f_ty, f_ty)
      | _ ->
        let cname = string_of_ident cname in
        if !tc_debug then begin
          Printf.fprintf stderr "Class table: \n";
          Ctbl.debug_print_ctbl stderr env.ctbl;
          Printf.fprintf stderr "\n";
        end;
        error_out (
          Printf.sprintf "Expected %s to be a field of class %s: (%s:%s).%s"
            f_str cname
            y_str (T.string_of_ity y_ty) f_str
        ) loc;
    end
  | _ ->
    match decl_class env.ctbl ~field:f with
    | Some cname ->
      error_out (got_but_expected y_ty (Tclass cname)) loc
    | None ->
      error_out (
        Printf.sprintf "Invalid heap location: %s.%s"
          y_str f_str
      ) loc

let tc_const_exp ce : T.const_exp T.t * ity =
  match ce.elt with
  | Enull     -> T.Enull     -: Tanyclass, Tanyclass
  | Eemptyset -> T.Eemptyset -: Trgn, Trgn
  | Eunit     -> T.Eunit     -: Tunit, Tunit
  | Eint i    -> T.Eint i    -: Tint, Tint
  | Ebool b   -> T.Ebool b   -: Tbool, Tbool

(* tc_exp G e = J

   Invariant:
   If G |- e : t then J = ok (e' : t, t) where e' = Annot(G, e).
*)
let rec tc_exp env e : (T.exp T.t * ity, string) result =
  match e.elt with
  | Econst e ->
    let e', e_ty = tc_const_exp e in
    ok (mk_const e', e_ty)
  | Evar x ->
    let* x_ty = find_in_ctxt env x e.loc in
    ok (mk_var x x_ty, x_ty)
  | Ebinop (op, e1, e2) ->
    let* e1', e1_ty = tc_exp env e1 in
    let* e2', e2_ty = tc_exp env e2 in
    begin match op with
      | Equal | Nequal ->
        let* () = match e1_ty with
          | Tint | Tbool | Trgn | Tunit | Tclass _ | Tanyclass | Tmath _ -> ok()
          | _ -> error_out "Cannot use = to compare non-values" e1.loc in
        let* () = expect_tys [e2.loc, e2_ty, e1_ty; e1.loc, e1_ty, e2_ty] in
        ok (mk_binop op e1' e2', T.Tbool)
      | _ ->
        let p1_ty, p2_ty, ret_ty = binop_ty op in
        let* () = expect_tys [e2.loc, e2_ty, p2_ty; e1.loc, e1_ty, p1_ty] in
        ok (mk_binop op e1' e2', ret_ty)
    end
  | Eunrop (op, e) ->
    let* e', e_ty = tc_exp env e in
    let p_ty, ret_ty = unrop_ty op in
    let* () = expect_ty e.loc e_ty p_ty in
    ok (mk_unrop op e', ret_ty)
  | Esingleton e ->
    let* e', e_ty = tc_exp env e in
    let* () = expect_ty_pred e.loc e_ty is_class_ty "<class>" in
    ok (mk_singleton e', T.Trgn)
  | Eimage (g, f) ->
    let* g', g_ty = tc_exp env g in
    let* () = expect_ty g.loc g_ty Trgn in
    if Ctbl.field_exists env.ctbl ~field:f
    then
      let field_ty = match Ctbl.field_type env.ctbl ~field:f with
        | Some ty -> ty
        | None -> assert false in
      ok (mk_image g' f field_ty, T.Trgn)
    else error_out (
        Printf.sprintf "Unknown field %s"
          (string_of_ident f)
           ) g.loc
  | Esubrgn (g, k) ->
     let* g', g_ty = tc_exp env g in
     let* () = expect_ty g.loc g_ty Trgn in
     if Ctbl.class_exists env.ctbl ~classname:k
     then ok (T.Esubrgn (g', k) -: Trgn, T.Trgn)
     else
       let cname = string_of_ident k in
       error_out (Printf.sprintf "Unknown class %s" cname) g.loc
  | Ecall (fn, args) ->
    let* (fn', args'), ret_ty = tc_exp_call env e.loc fn args in
    ok (T.Ecall (fn', args') -: ret_ty, ret_ty)

and tc_exp_call env loc fn args : ((ident T.t * T.exp T.t list) * ity, string) result =
  let open List in
  let fn_name = string_of_ident fn in
  match tc_exp_call_special env loc fn args with
  | Ok res -> ok res
  | Error msg -> Error msg
  | exception _ ->
    let* fn_ty = find_in_ctxt env fn loc in
    match fn_ty with
    | Tfunc {params; ret} | Tmeth {params; ret} ->
      let args_len, params_len = length args, length params in
      if args_len <> params_len
      then expected_n_args loc fn_name params_len args_len
      else
        let* arg_jdms = sequence (map (tc_exp env) args) in
        let arg_exps, arg_tys = split arg_jdms in
        let arg_tys_locs = combine (map (fun e -> e.loc) args) arg_tys in
        let check_list = combine arg_tys_locs params in
        let check = map (fun ((e,t),p) -> (e,t,p)) check_list in
        let* () = expect_tys check in
        (* At this point, the call exp is well-typed. *)
        let fn' = fn -: fn_ty in
        ok ((fn', arg_exps), ret)
    | _ -> error_out (Printf.sprintf "Unknown method %s" fn_name) loc

and tc_exp_call_special env loc fn args
  : ((ident T.t * T.exp T.t list) * ity, string) result =
  let fn_name = string_of_ident fn in
  match fn with
  | Id "make" ->
    begin match args with
      | [size; default] ->
        let* size', size_ty = tc_exp env size in
        let* default', default_ty = tc_exp env default in
        let* () = expect_ty size.loc size_ty Tint in
        let ret = T.Tmath (Id "array", Some default_ty) in
        let fn' = fn -: ret in
        ok ((fn', [size'; default']), ret)
      | args -> expected_n_args loc fn_name 2 (List.length args)
    end
  | Id "length" ->
    begin match args with
      | [arr] ->
        let* arr', arr_ty = tc_exp env arr in
        let* ()   = expect_ty_pred arr.loc arr_ty is_array_ty "array" in
        let fn_ty = T.Tfunc { params = [arr_ty] ; ret = Tint } in
        let fn'   = fn -: fn_ty in
        ok ((fn', [arr']), T.Tint)
      | args -> expected_n_args loc fn_name 1 (List.length args)
    end
  | Id "get" ->
    begin match args with
      | [arr; idx] ->
        let* arr', arr_ty = tc_exp env arr in
        let* idx', idx_ty = tc_exp env idx in
        let* () = expect_ty idx.loc idx_ty Tint in
        let* () = expect_ty_pred arr.loc arr_ty is_array_ty "array" in
        let ret = math_array_base_ty arr_ty in
        let fn' = fn -: T.Tfunc { params = [arr_ty; idx_ty] ; ret } in
        ok ((fn', [arr'; idx']), ret)
      | args -> expected_n_args loc fn_name 2 (List.length args)
    end
  | Id "set" ->
    begin match args with
      | [arr; idx; elt] ->
        let* arr', arr_ty = tc_exp env arr in
        let* idx', idx_ty = tc_exp env idx in
        let* elt', elt_ty = tc_exp env elt in
        let* () = expect_ty idx.loc idx_ty Tint in
        let* () = expect_ty_pred arr.loc arr_ty is_array_ty "array" in
        let bty = math_array_base_ty arr_ty in
        let* () = expect_ty elt.loc elt_ty bty in
        let ret = arr_ty in
        let fn' = fn -: T.Tfunc { params = [arr_ty; idx_ty; elt_ty] ; ret } in
        ok ((fn', [arr'; idx'; elt']), ret)
      | args -> expected_n_args loc fn_name 3 (List.length args)
    end
  | _ -> failwith @@ "tc_exp_call_special: Unknown function " ^ fn_name

(* tc_array_location G loc a e = J

   If G |- a[e] : t then J = ok ((a : t array)[idx : int] : t, t);
   otherwise J is an error message with location loc.
*)
let tc_array_location env loc arr idx
  : ((ident T.t * T.exp T.t) T.t * ity, string) result =
  let* arr_ty = find_in_ctxt env arr loc in
  match arr_ty with
  | Tclass cname when Ctbl.is_array_like_class env.ctbl ~classname:cname ->
    let* idx', idx_ty = tc_exp env idx in
    let* ()  = expect_ty idx.loc idx_ty Tint in
    let arr' = arr -: arr_ty in
    let base_ty =
      match Ctbl.element_type env.ctbl ~classname:cname with
      | Some ty -> ty
      | _ -> assert false in
    ok ((arr', idx') -: base_ty, base_ty)
  | _ -> error_out (expected_msg (T.string_of_ity arr_ty) "<array>") loc

let add_quantifier_bindings env qbinds : (tenv * T.qbinders, string) result =
  let walk {name; ty; in_rgn; is_non_null} acc =
    let* () = wf_ident ty.loc name in
    let* env, binders = acc in
    match ty.elt, in_rgn with
    | Tctor (cname, []), Some r 
        when Ctbl.class_exists env.ctbl ~classname:cname ->
      let* r', r_ty = tc_exp env r in
      let* () = expect_ty r.loc r_ty Trgn in
      let ty' = ity_of_ty env ty.elt in
      let binder = T.{name=name -: ty'; in_rgn=Some r'; is_non_null} in
      ok (add_to_ctxt env name ty', binder :: binders)
    | _, None ->
      let* () = ensure_type_is_known env ty in
      let ty' = ity_of_ty env ty.elt in
      let binder = T.{name=name -: ty'; in_rgn=None; is_non_null} in
      ok (add_to_ctxt env name ty', binder :: binders)
    | _, Some _ ->
      let msg = Printf.sprintf "Expected %s to be of class type" in
      error_out (msg % string_of_ty @@ ty) ty.loc
  in foldr walk (ok (env, [])) qbinds

(* tc_let_bound_value G loc l aty = J

   Invariant:
   If aty = Some t and G |- l : t, then J = ok ((l : t) : t, t); otherwise
   J is an error message with location loc.

   If aty = None, then if exists t such that G |- l : t,
   then J = ok ((l : t) : t, t)
*)
let tc_let_bound_value env loc lb annot
  : (T.let_bound_value T.t * ity, string) result =
  let check ty =
    match annot with
    | Some ty' ->
      let ty' = ity_of_ty env ty'.elt in
      expect_ty loc ty' ty >> ok ty'
    | None -> ok ty in
  match lb.elt with
  | Lloc (y, fld) ->
    let* hloc', fld_ty = tc_heap_location env lb.loc y fld in
    let y', fld' = hloc'.node in
    let* ty = check fld_ty in
    ok (T.Lloc (y', fld') -: ty, ty)
  | Larr (a, idx) ->
    let* aloc', base_ty = tc_array_location env lb.loc a idx in
    let a', idx' = aloc'.node in
    let* ty = check base_ty in
    ok (T.Larr (a', idx') -: ty, ty)
  | Lexp e ->
    let* e', e_ty = tc_exp env e in
    let* ty = check e_ty in
    ok (T.Lexp e' -: ty, ty)

(* tc_formula G f = J

   Invariant:
   If G |- f, then J = ok f' where f' = Annot(G, f)
*)
let rec tc_formula env f : (T.formula, string) result =
  match f.elt with
  | Ftrue  -> ok T.Ftrue
  | Ffalse -> ok T.Ffalse
  | Finit e ->
    let* e', e_ty = tc_let_bound_value env e.loc e None in ok (T.Finit e')
  | Fexp {elt=Econst {elt=Ebool true; _}; _} -> ok T.Ftrue
  | Fexp {elt=Econst {elt=Ebool false; _}; _} -> ok T.Ffalse
  | Fexp e ->
    let* e', e_ty = tc_exp env e in
    let p = function T.Tbool | Tprop -> true | _ -> false in
    let* () = expect_ty_pred e.loc e_ty p "bool or <prop>" in
    ok (T.Fexp e')
  | Fnot f ->
    let* f' = tc_formula env f in
    ok (T.Fnot f')
  | Fpointsto (x, fld, e) ->
    let* x_ty = find_in_ctxt env x f.loc in
    let* e', e_ty = tc_exp env e in
    let* {node=(x',fld'); _}, fld_ty = tc_heap_location env f.loc x fld in
    let* () = expect_ty e.loc e_ty fld_ty in
    ok (T.Fpointsto (x', fld', e'))
  | Farray_pointsto (a, idx, e) ->
    let* {node=(a',idx'); _}, base_ty = tc_array_location env f.loc a idx in
    let* e', e_ty = tc_exp env e in
    let* () = expect_ty e.loc e_ty base_ty in
    ok (T.Farray_pointsto (a', idx', e'))
  | Fsubseteq (e1, e2) ->
    let* e1', e1_ty = tc_exp env e1 in
    let* e2', e2_ty = tc_exp env e2 in
    let* () = expect_tys [e1.loc, e1_ty, Trgn; e2.loc, e2_ty, Trgn] in
    ok (T.Fsubseteq (e1', e2'))
  | Fdisjoint (e1, e2) ->
    let* e1', e1_ty = tc_exp env e1 in
    let* e2', e2_ty = tc_exp env e2 in
    let* () = expect_tys [e1.loc, e1_ty, Trgn; e2.loc, e2_ty, Trgn] in
    ok (T.Fdisjoint (e1', e2'))
  | Fmember (e1, e2) ->
    let* e1', e1_ty = tc_exp env e1 in
    let* e2', e2_ty = tc_exp env e2 in
    let* () = expect_ty_pred e1.loc e1_ty is_class_ty "<class>" in
    let* () = expect_ty e2.loc e2_ty Trgn in
    ok (T.Fmember (e1', e2'))
  | Fconn (c, f1, f2) ->
    let* f1' = tc_formula env f1 in
    let* f2' = tc_formula env f2 in
    ok (T.Fconn (c, f1', f2'))
  | Fold (e, valu) ->
    let* e', e_ty = tc_exp env e in
    let* valu', valu_ty = tc_let_bound_value env f.loc valu None in
    let* () = expect_ty e.loc e_ty valu_ty in
    ok (T.Fold (e', valu'))
  | Ftype (g, ty) ->            (* ty has to be of class type *)
    let* g', g_ty = tc_exp env g in
    let* _ = sequence (List.map (ensure_class_exists env g.loc) ty) in
    let* () = expect_ty g.loc g_ty Trgn in
    ok (T.Ftype (g', ty))
  | Flet (x, tyopt, { value = valu; is_old; is_init }, frm) ->
    assert ((is_old && not is_init) ||
            (not is_old && is_init) ||
            (not is_old && not is_init));
    let* () = wf_ident f.loc x in
    let* valu', valu_ty = tc_let_bound_value env f.loc valu tyopt in
    let env' = add_to_ctxt env x valu_ty in
    let* frm' = tc_formula env' frm in
    let valu' = T.{ value = valu'; is_old; is_init } -: valu_ty in
    ok (T.Flet (x -: valu_ty, valu', frm'))
  | Fquant (q, bindings, frm) ->
    let* new_env, binders = add_quantifier_bindings env bindings in
    let* frm' = tc_formula new_env frm in
    ok (T.Fquant (q, binders, frm'))

(* tc_named_formula G nf = J

   Invariant:
   If nf is a well-typed axiom or lemma, J = ok nf' where nf' = Annot(G, nf).

   If nf is a predicate, the type associated with nf.formula_name is params ->
   Tprop where params is a list of annotated idents (parameters of nf)
*)
let rec tc_named_formula env nf : (T.named_formula, string) result =
  let open List in
  let* () = wf_ident nf.loc nf.elt.formula_name in
  let nf,loc = nf.elt,nf.loc in
  match nf.kind with
  | `Axiom | `Lemma ->
    let nf_ty = T.Tprop in
    let env = add_to_ctxt env nf.formula_name nf_ty in
    let* frm' = tc_formula env nf.body in
    let fname = nf.formula_name -: Tprop in
    ok T.{ kind = nf.kind;
           formula_name = fname;
           annotation = nf.annotation;
           params = [];
           body = frm' }
  | `Predicate ->
    let* () = wf_invariant_params loc nf in
    let param_names, param_tys = split nf.params in
    let names = combine (map (fun p -> p.loc) param_tys) param_names in
    let* _ = sequence @@ map (uncurry wf_ident) names in
    let* _ = sequence @@ map (ensure_type_is_known env) param_tys in
    let param_tys = map (ity_of_ty env) @@ get_elts param_tys in
    let params = combine param_names param_tys in
    let pred_ty = T.Tfunc { params = param_tys; ret = Tprop } in
    let env = fold_right (fun (n,t) env -> add_to_ctxt env n t) params env in
    let env = add_to_ctxt env nf.formula_name pred_ty in
    let* frm' = tc_formula env nf.body in
    let fname = nf.formula_name -: pred_ty in
    let params' = map (uncurry ( -: )) params in
    ok T.{kind = nf.kind;
          formula_name = fname;
          annotation = nf.annotation;
          params = params';
          body = frm'}

and wf_invariant_params loc nf : (unit,string) result =
  let open Printf in
  let string_of_fannot = function
    | Public_invariant -> "public"
    | Private_invariant -> "private" in
  if nf.annotation <> None && length nf.params <> 0
  then
    let msg = sprintf "%s invariant %s cannot have parameters\n" in
    let invknd = string_of_fannot (Option.get nf.annotation) in
    error_out (msg invknd (string_of_ident nf.formula_name)) loc
  else ok ()

let rec tc_inductive_predicate env ind : (T.inductive_predicate, string) result =
  let open List in
  let ind, loc = ind.elt, ind.loc in
  let* () = wf_ident loc ind.ind_name in
  let param_names, param_tys = split ind.ind_params in
  let names = combine (map (fun p -> p.loc) param_tys) param_names in
  let* _ = sequence @@ map (uncurry wf_ident) names in
  let* _ = sequence @@ map (ensure_type_is_known env) param_tys in
  let param_tys = map (ity_of_ty env) @@ get_elts param_tys in
  let params = combine param_names param_tys in
  let ind_ty = T.Tfunc { params = param_tys; ret = Tprop } in
  let env = foldr (fun (n,t) env -> add_to_ctxt env n t) env params in
  let env = add_to_ctxt env ind.ind_name ind_ty in
  let check_case (id, frm) =
    let* () = wf_ident id.loc id.elt in
    let* frm = tc_formula env frm in
    ok (id.elt, frm) in
  let* ind_cases = sequence @@ map check_case ind.ind_cases in
  ok T.{ind_name = ind.ind_name -: ind_ty;
        ind_params = map (uncurry (-:)) params;
        ind_cases = ind_cases }

let wf_effect_elt env eff : (unit, string) result =
  let rec ensure_no_datagroup_uses exp =
    match exp.elt with
    | Econst _ | Evar _ -> ok ()
    | Ebinop (_, e1, e2) ->
      let* () = ensure_no_datagroup_uses e1 in
      ensure_no_datagroup_uses e2
    | Eunrop (_, e) -> ensure_no_datagroup_uses e
    | Esingleton e -> ensure_no_datagroup_uses e
    | Ecall (_, es) ->
      let* _ = sequence (List.map ensure_no_datagroup_uses es) in
      ok ()
    | Esubrgn (g, k) -> ensure_no_datagroup_uses g
    | Eimage (g, f) ->
      if not (is_datagroup f)
      then ensure_no_datagroup_uses g
      else error_out
          (Printf.sprintf "Cannot use datagroup %s for its l-value"
             (string_of_ident f))
          g.loc in
  let {effect_kind; effect_desc} = eff.elt in
  match effect_desc with
  | Effvar id -> ok ()
  | Effimg (g, f) -> ensure_no_datagroup_uses g

(* tc_effect G es = J

   Invariant:
   If G |- es, then J = ok es' where,
   for each x in es,   es' contains (x : t) where G |- x : t
   for each g`f in es, es' contains ((g : Trgn)`(f : FieldType(G, f)) : Trgn)
*)
let rec tc_effect env (es: effect node) : (T.effect, string) result =
  match es.elt with
  | [] -> ok []
  | ({elt={effect_desc=eff; effect_kind=kind}; loc} as eff_elt) :: es ->
    let* es' = tc_effect env {elt=es; loc} in
    let* () = wf_effect_elt env eff_elt in
    match eff with
    | Effvar id ->
      let* id_ty = find_in_ctxt env id loc in
      let desc = T.Effvar (id -: id_ty) -: id_ty in
      let eff' = T.{effect_kind = kind; effect_desc = desc} in
      ok (eff' :: es')
    | Effimg (g, f) ->
      let* g', g_ty = tc_exp env g in
      let* () = expect_ty g.loc g_ty Trgn in
      if (Ctbl.field_exists env.ctbl ~field:f || is_datagroup f)
      then let field_ty = match Ctbl.field_type env.ctbl ~field:f with
          | Some ty -> ty
          | None -> Tdatagroup in
        let f' = f -: field_ty in
        let desc = T.Effimg (g', f') -: Trgn in
        let eff' = T.{effect_kind = kind; effect_desc = desc} in
        ok (eff' :: es')
      else
        error_out (
          Printf.sprintf "Unknown field or datagroup %s"
            (string_of_ident f)
        ) g.loc

let wf_call_args env args : (unit,string) result =
  let rec check_arg arg = match arg.elt with
    | Evar x -> ok ()
    | _ -> error_out "Argument to method call must be a variable" arg.loc in
  let* _ = sequence (List.map check_arg args) in
  ok ()

let method_args_of_ast_exps exps =
  foldr (fun elt acc -> match elt.elt with
      | Evar x -> {elt = x; loc = elt.loc} :: acc
      | _ -> invalid_arg "method_args_of_ast_exps"
    ) [] exps

let rec tc_atomic_command env c : (T.atomic_command, string) result =
  let open List in
  match c.elt with
  | Skip -> ok T.Skip
  | Assign (x, {elt = Ecall(fn, args)}) -> (* method call *)
    let* () = wf_call_args env args in
    let args' = method_args_of_ast_exps args in
    let node = Call (Some x, fn, args') in
    tc_atomic_command env {elt = node; loc = c.loc}
  | Assign (x, e) ->
    let* x_ty = find_in_ctxt env x c.loc in
    let* e', e_ty = tc_exp env e in
    let* () = expect_ty c.loc x_ty e_ty in
    ok (T.Assign (x -: x_ty, e'))
  | Havoc x ->
    let* x_ty = find_in_ctxt env x c.loc in
    ok (T.Havoc (x -: x_ty))
  | New_class (x, k) ->
    let* x_ty = find_in_ctxt env x c.loc in
    let* () = ensure_class_exists env c.loc k in
    let* () = expect_ty c.loc x_ty (Tclass k) in
    ok (T.New_class (x -: Tclass k, k))
  | New_array (x, k, sz) ->
    let* x_ty = find_in_ctxt env x c.loc in
    let* sz', sz_ty = tc_exp env sz in
    let* () = expect_ty c.loc sz_ty Tint in
    let* () = ensure_class_exists env c.loc k in
    let* () = expect_ty c.loc x_ty (Tclass k) in
    ok (T.New_array (x -: Tclass k, k, sz'))
  | Field_deref (x, y, f) ->    (* x := y.f *)
    let* {node=y',f'; _}, fld_ty = tc_heap_location env c.loc y f in
    let* x_ty = find_in_ctxt env x c.loc in
    let* () = expect_ty c.loc x_ty fld_ty in
    ok (T.Field_deref (x -: x_ty, y', f'))
  | Field_update (x, f, e) ->   (* x.f := e *)
    let* {node=x',f'; _}, fld_ty = tc_heap_location env c.loc x f in
    let* e', e_ty = tc_exp env e in
    let* () = expect_ty c.loc fld_ty e_ty in
    ok (T.Field_update (x', f', e'))
  | Array_access (x, arr, idx) -> (* x := arr[idx] *)
    let* {node=a',idx'; _}, base_ty = tc_array_location env c.loc arr idx in
    let* x_ty = find_in_ctxt env x c.loc in
    let* () = expect_ty c.loc x_ty base_ty in
    ok (T.Array_access (x -: x_ty, a', idx'))
  | Array_update (arr, idx, e) -> (* arr[idx] := e *)
    let* {node=a',idx'; _}, base_ty = tc_array_location env c.loc arr idx in
    let* e', e_ty = tc_exp env e in
    let* () = expect_ty c.loc base_ty e_ty in
    ok (T.Array_update (a', idx', e'))
  | Call (xopt, meth, args) ->
    let args = exps_of_method_args args in
    (* FIXME: Don't use tc_exp_call? *)
    let* (meth', args'), ret_ty = tc_exp_call env c.loc meth args in
    let args' = method_args_of_exps args' in
    begin match ret_ty, xopt with
      | Tprop, _ ->
        error_out (
          Printf.sprintf "Cannot use predicate %s as a method"
            (string_of_ident meth)
        ) c.loc
      | _, Some x ->
        let* x_ty = find_in_ctxt env x c.loc in
        let* () = expect_ty c.loc x_ty ret_ty in
        ok (T.Call (Some (x -: x_ty), meth', args'))
      | _, None ->
        let* () = expect_ty c.loc ret_ty Tunit in
        ok (T.Call (None, meth', args'))
    end

and exps_of_method_args args =
  List.map (fun {elt; loc} -> {elt = Evar elt; loc}) args

and method_args_of_exps exps =
  List.map (fun T.{node; ty} -> match node with
      | T.Evar x -> x
      | _ -> invalid_arg "method_args_of_exps"
    ) exps

(* tc_command G c = J

   Invariant:
   If G |- c, then J = ok c' where c' = Annot(G, c).
*)
let rec tc_command env c : (T.command, string) result =
  match c.elt with
  | Acommand ac ->
    let* ac' = tc_atomic_command env ac in
    ok (T.Acommand ac')
  | Vardecl (x, modif, ty, c) ->
    let* () = ensure_type_is_known env ty in
    let* () = wf_ident c.loc x in
    let ty = ity_of_ty env ty.elt in
    let env' = add_to_ctxt env x ty in
    let* c' = tc_command env' c in
    ok (T.Vardecl (x -: ty, modif, ty, c'))
  | Seq (c1, c2) ->
    let* c1' = tc_command env c1 in
    let* c2' = tc_command env c2 in
    ok (T.Seq (c1', c2'))
  | If (e, c1, c2) ->
    let* e', e_ty = tc_exp env e in
    let* () = expect_ty e.loc e_ty Tbool in
    let* c1' = tc_command env c1 in
    let* c2' = tc_command env c2 in
    ok (T.If (e', c1', c2'))
  | While (e, ws, c) ->
    let* e', e_ty = tc_exp env e in
    let* () = expect_ty e.loc e_ty Tbool in
    let* ws = tc_while_spec env ws in
    let* c' = tc_command env c in
    ok (T.While (e', ws, c'))
  | Assume f ->
    let* f' = tc_formula env f in
    ok (T.Assume f')
  | Assert f ->
    let* f' = tc_formula env f in
    ok (T.Assert f')

and tc_while_spec env ws : (T.while_spec, string) result =
  let rec check invs eff v = function
    | [] -> ok (invs, eff, v)
    | {elt = Wvariant e} :: rest ->
      let* e, _ = tc_exp env e in check invs eff (Some e) rest
    | {elt = Winvariant f} :: rest ->
      let* f = tc_formula env f in check (f :: invs) eff v rest
    | {elt = Wframe e} :: rest ->
      let* e = tc_effect env e in check invs (e @ eff) v rest
  in
  if is_nil ws then ok T.{winvariants = []; wframe = []; wvariant = None}
  else
    let* invs, eff, v = check [] [] None ws in
    ok T.{winvariants = rev invs; wframe = eff; wvariant = v}

let rec tc_spec env s : (T.spec, string) result =
  match s.elt with
  | [] -> ok []
  | {elt; loc} :: ss ->
    let* ss' = tc_spec env {elt=ss; loc} in
    match elt with
    | Precond f ->
      let* f' = tc_formula env f in
      ok (T.Precond f' :: ss')
    | Postcond f ->
      let* f' = tc_formula env f in
      ok (T.Postcond f' :: ss')
    | Effects es ->
      let* es' = tc_effect env es in
      ok (T.Effects es' :: ss')

let tc_boundary env b : (T.boundary_decl, string) result =
  let effects =
    List.map (fun e ->
        {elt = {effect_kind = Read; effect_desc = e.elt};
         loc = e.loc}
      ) b.elt in
  let effects = {elt = effects; loc = b.loc } in
  let* effs' = tc_effect env effects in
  ok (List.map (fun T.{effect_desc;_} -> effect_desc) effs')

let tc_meth_decl env mdecl : (tenv * T.meth_decl, string) result =
  let open List in
  let rec add_params env = function (* Need to get annotated param infos *)
    | [] -> env, []
    | ({param_name; param_ty={elt=ty;_}; _} as p) :: ps ->
      let pty = ity_of_ty env ty in
      let env, pinfos = add_params env ps in
      let env' = add_to_ctxt env param_name pty in
      let pinfo =
        T.{param_name = param_name -: pty;
           param_modifier = p.param_modifier;
           param_ty = pty;
           is_non_null = p.is_non_null} in
      env', pinfo :: pinfos in
  let* () = wf_ident mdecl.loc mdecl.elt.meth_name in
  (* Check parameter names don't clash with Why3 keywords *)
  let param_names =
    map (fun p -> (p.param_ty.loc, p.param_name)) mdecl.elt.params in
  let* _ = sequence (map (uncurry wf_ident) param_names) in
  let param_tys = map (fun p -> p.param_ty) mdecl.elt.params in
  let* _ = sequence (map (ensure_type_is_known env) param_tys) in
  (* Type check meth decl in a tenv with parameters known *)
  let env, params = add_params env mdecl.elt.params in
  let* () = ensure_type_is_known env mdecl.elt.result_ty in
  let res_ty = ity_of_ty env mdecl.elt.result_ty.elt in
  let env = add_to_ctxt env (Id "result") res_ty in
  let* spec' = tc_spec env mdecl.elt.meth_spec in
  let ptys' = map (fun T.{param_ty;_} -> param_ty) params in
  let non_null_result = is_class_ty res_ty && mdecl.elt.result_is_non_null in
  let mdecl' =
    T.{meth_name = mdecl.elt.meth_name -: Tmeth {params=ptys'; ret=res_ty};
       params = params;
       result_ty = res_ty;
       result_is_non_null = non_null_result;
       (* NOTE: the can_diverge field is initially marked as false.  Later,
          we'll perform some analyses to figure out whether a method can
          diverge. *)
       can_diverge = false;
       meth_spec = spec'} in
  ok (env, mdecl')

let tc_meth_def env mdef : (T.meth_def, string) result =
  let (Method (mdecl, copt)) = mdef.elt in
  let* env', mdecl' = tc_meth_decl env mdecl in
  match copt with
  | Some c -> let* c' = tc_command env' c in ok (T.Method (mdecl', Some c'))
  | None -> ok (T.Method (mdecl', None))

let tc_extern env extern : (tenv * T.extern_decl, string) result =
  let* () = wf_ident extern.loc extern.elt.extern_symbol in
  let inp = get_elts extern.elt.extern_input in
  let params = List.map (ity_of_ty env) inp in
  let name = extern.elt.extern_symbol in
  let assert_is_some e = assert (match e with Some _ -> true | _ -> false) in
  match extern.elt.extern_kind with
  | Ex_type ->
    let ty = Tctor(name, []) in
    if is_known_type env ty
    then error_out (
        Printf.sprintf "Type %s has already been defined"
          (string_of_ty (no_loc ty))
      ) extern.loc
    else
      let env' = {env with exts = name :: env.exts} in
      assert_is_some extern.elt.extern_default;
      let default = Option.get extern.elt.extern_default in
      let ty = ity_of_ty env' ty in
      let env' = add_to_ctxt env' default ty in
      ok (env', T.Extern_type (name, default))
  | Ex_axiom ->
    let env' = add_to_ctxt env name Tprop in
    ok (env', T.Extern_axiom name)
  | Ex_lemma ->
    let env' = add_to_ctxt env name Tprop in
    ok (env', T.Extern_lemma name)
  | Ex_function ->
    assert_is_some extern.elt.extern_output;
    let ret = Option.get extern.elt.extern_output in
    let ret = ity_of_ty env ret.elt in
    let func_ty = T.Tfunc {params; ret} in
    let env' = add_to_ctxt env name func_ty in
    ok (env', T.(Extern_function {name; params; ret}))
  | Ex_const ->
    assert_is_some extern.elt.extern_output;
    let out = Option.get extern.elt.extern_output in
    let const_ty = ity_of_ty env out.elt in
    let env' = add_to_ctxt env name const_ty in
    ok (env', T.Extern_const (name, const_ty))
  | Ex_predicate ->
    let pred_ty = T.Tfunc {params; ret=Tprop} in
    let env' = add_to_ctxt env name pred_ty in
    ok (env', T.Extern_predicate {name; params})
  | Ex_bipredicate ->
    let msg = "May only use extern bipredicates within a bimodule" in
    error_out msg extern.loc

let wf_field_decl env classname fdecl : (unit, string) result =
  let* () = wf_ident fdecl.loc fdecl.elt.field_name in
  let ty = fdecl.elt.field_ty in
  match ty.elt with
  | Tctor(cname,[]) when cname = classname -> ok ()
  | _ -> ensure_type_is_known env ty

let wf_cdecl (env: tenv) (cdecl: class_decl node) : (unit, string) result =
  let open List in
  let cname = cdecl.elt.class_name in
  let* () = wf_ident cdecl.loc cname in
  let* _ = sequence @@ map (wf_field_decl env cname) cdecl.elt.fields in
  ok ()

let tc_cdecl env cdecl : (T.class_decl, string) result =
  let* () = wf_cdecl env cdecl in
  let class_name = cdecl.elt.class_name in
  let of_field_decl {elt={field_name; field_ty; attribute}; loc} =
    let f_ty = match field_ty.elt with
      | Tctor(cname,[]) when cname = class_name -> T.Tclass cname
      | _ -> ity_of_ty env field_ty.elt in
    T.{field_name = field_name -: f_ty; field_ty = f_ty; attribute} in
  let fields = List.map of_field_decl cdecl.elt.fields in
  ok T.{class_name; fields}

let wf_vdecl (env: tenv) (m: modifier) (id: ident) (ty: ty node)
  : (unit, string) result =
  (* FIXME: location info is approximate *)
  let* () = wf_ident ty.loc id in
  ensure_type_is_known env ty

let equal_meth_decl (m: meth_decl node) (m': meth_decl node)
  : (unit, string) result =
  let m_params, m'_params = m.elt.params, m'.elt.params in
  let m_len, m'_len = List.length m_params, List.length m'_params in
  if m_len <> m'_len
  then error_out
      (Printf.sprintf
         "Method %s requires %d parameters"
         (string_of_ident m.elt.meth_name)
         m_len)
      m'.loc
  else
    (* ensure result types are the same *)
  if not (equal_ty m.elt.result_ty m'.elt.result_ty)
  || m.elt.result_is_non_null <> m'.elt.result_is_non_null
  then error_out
      (Printf.sprintf
         "Return type mismatch: expected method %s to return %s%s"
         (string_of_ident m'.elt.meth_name)
         (string_of_ty m.elt.result_ty)
         (if m.elt.result_is_non_null then "+" else ""))
      m'.elt.result_ty.loc
  else
    (* check each parameter has the same name and type and appears in
       the same order *)
    let params = List.combine m_params m'_params in
    List.fold_left (fun res (p, p') ->
        if equal_param_info p p'
        then ok ()
        else error_out
            (Printf.sprintf
               "Parameter mismatch: expected parameter %s with \
                type %s%s%s"
               (string_of_ident p.param_name)
               (string_of_ty p.param_ty)
               (if p.is_non_null then "+" else "")
               (match p.param_modifier with
                | None -> ""
                | Some m -> " and status " ^ string_of_modifier m))
            p.param_ty.loc
      ) (ok ()) params

(* Check whether each field of [c] that also appears in [c'] has the
   same type and attribute. *)
let cdecl_equal_fields (c: class_decl node) (c': class_decl node) =
  let flds, flds' = c.elt.fields, c'.elt.fields in
  List.for_all (fun f ->
      let fname = f.elt.field_name in
      match List.find (fun f' -> f'.elt.field_name = fname) flds' with
      | f' -> equal_field f f'
      | exception Not_found -> false
    ) flds

let wf_interface_module_cdecl intr_cdecl mdl_cdecl : (unit,string) result =
  if cdecl_equal_fields intr_cdecl mdl_cdecl then ok () else
    let cname = string_of_ident intr_cdecl.elt.class_name in
    let cloc = intr_cdecl.loc in
    error_out (Printf.sprintf "Class declaration mismatch %s" cname) cloc

let wf_interface_module
    (env: tenv)
    (intr: interface_def node)
    (mdl: module_def node)
  : (unit, string) result =
  let open List in
  let mdl_name = string_of_ident mdl.elt.mdl_name in
  (* 1. Module defines every method that the interface defines *)
  (* 2. Each method that the module defines has the same ity *)
  let wf_methods intr_meths mdl_meths : (unit, string) result =
    let find_same_meth meth_name =
      find (fun (Method (mdl_meth, _)) ->
          mdl_meth.elt.meth_name = meth_name
        ) (get_elts mdl_meths) in
    fold_left (fun acc intr_meth ->
        let intr_meth_name = intr_meth.elt.meth_name in
        match find_same_meth intr_meth_name with
        | Method (mdl_meth, _) ->
          equal_meth_decl intr_meth mdl_meth >> acc
        | exception Not_found ->
          error_out
            (Printf.sprintf "Module %s does not implement method %s"
               mdl_name (string_of_ident intr_meth_name))
            intr_meth.loc
      ) (ok ()) intr_meths in
  (* 3. Module defines every class that the interface defines *)
  (* 4. Each class has the same public and ghost fields *)
  let wf_classes intr_cdecls mdl_cdefs : (unit, string) result =
    let find_same_class class_name =
      find (fun (Class cdecl) ->
          cdecl.elt.class_name = class_name
        ) (get_elts mdl_cdefs) in
    fold_left (fun acc intr_class ->
        let intr_class_name = intr_class.elt.class_name in
        match find_same_class intr_class_name with
        | Class cdecl -> wf_interface_module_cdecl intr_class cdecl >> acc
        | exception Not_found -> ok ()
          (* [2024-08-18] CHANGED: Ok for module to not repeat class decl. *)
          (* error_out *)
          (*   (Printf.sprintf "Module %s does not define class %s" *)
          (*      mdl_name (string_of_ident intr_class_name)) *)
          (*   intr_class.loc *)
      ) (ok ()) intr_cdecls in
  (* 5. Each datagroup declared in the interface is defined in the module *)
  let wf_datagroups intr_grps mdl_grps : (unit, string) result =
    fold_left (fun acc d ->
        if not (List.exists (fun d' -> d = d') mdl_grps)
        then error
            (Printf.sprintf "Error: Module %s does not define datagroup %s"
               mdl_name (string_of_ident d))
        else acc
      ) (ok ()) intr_grps in
  let intr_meths = interface_methods intr in
  let intr_cdecls = interface_classes intr in
  let intr_grps = interface_datagroups intr in
  let mdl_meths = module_methods mdl in
  let mdl_cdefs = module_classes mdl in
  let mdl_grps = module_datagroup_names mdl in
  let* () = wf_methods intr_meths mdl_meths in
  let* () = wf_classes intr_cdecls mdl_cdefs in
  let* () = wf_datagroups intr_grps mdl_grps in
  ok ()

(* Check if [intr_def] imports interface [name] *)
let interface_does_import (intr_def: interface_def node) (name: ident) : bool =
  let imports_name = function
    | {elt = Intr_import {elt = {import_kind = Iregular; import_name}}} ->
      import_name = name
    | _ -> false in
  exists imports_name intr_def.elt.intr_elts

let module_does_import (mdl_def: module_def node) (name: ident) : bool =
  let imports_name = function
    | {elt = Mdl_import {elt = {import_kind = Iregular; import_name}}} ->
      import_name = name
    | _ -> false in
  exists imports_name mdl_def.elt.mdl_elts

let wf_import loc import : (unit,string) result =
  let open Printf in
  let {import_kind; import_name; import_as; related_by} = import in
  let name = string_of_ident import_name in
  if import_kind = Itheory && Option.is_some related_by then
    let msg = sprintf "Theory import %s cannot be related by %s\n" in
    error_out (msg name (string_of_ident (Option.get related_by))) loc else
  if Option.is_some import_as then
    let msg = sprintf "Qualified import (%s as %s) not currently allowed\n" in
    error_out (msg name (string_of_ident (Option.get import_as))) loc
  else ok ()

let wf_interface_annotations intr_def : (unit,string) result =
  let open Printf in
  let name = string_of_ident intr_def.elt.intr_name in
  let loc = intr_def.loc in
  let no_private nf = match nf.elt.annotation with
    | None | Some Public_invariant -> ok ()
    | Some Private_invariant ->
      let msg = sprintf "Predicate %s in %s cannnot be annotated as private" in
      error_out (msg (string_of_ident nf.elt.formula_name) name) loc in
  let preds = interface_predicates intr_def in
  let* _ = sequence (List.map no_private preds) in
  let pub = filter (fun e -> e.elt.annotation = Some Public_invariant) preds in
  if length pub <= 1 then ok () else
  error_out (sprintf "%s cannot have more than one public invariant" name) loc

(* Type check and build a tenv from an interface definition.  Requires
   a program environment to access definitions of imported interfaces.
*)
let rec tc_interface penv tenv intr_def
  : (tpenv * tenv * T.interface_def, string) result =
  let intr_name = intr_def.elt.intr_name in
  let* () = wf_ident intr_def.loc intr_name in
  let* () = wf_interface_annotations intr_def in
  let walk penv env elt : (tpenv * tenv * T.interface_elt, string) result =
    match elt.elt with
    | Intr_cdecl cdecl ->
      let* cdecl' = tc_cdecl env cdecl in
      let ctbl = Ctbl.add env.ctbl cdecl' in
      ok (penv, {env with ctbl}, T.Intr_cdecl cdecl')
    | Intr_vdecl (m, id, ty) ->
      let* () = wf_vdecl env m id ty in
      let vty = ity_of_ty env ty.elt in
      let new_env = add_to_ctxt env id vty in
      let elt' = T.Intr_vdecl (m, id -: vty, vty) in
      ok (penv, new_env, elt')
    | Intr_mdecl mdecl ->
      let* _, mdecl' = tc_meth_decl env mdecl in
      let meth_ty = ity_of_meth_decl env mdecl.elt in
      let new_env = add_to_ctxt env mdecl.elt.meth_name meth_ty in
      ok (penv, new_env, T.Intr_mdecl mdecl')
    | Intr_boundary b ->
      let* b' = tc_boundary env b in
      ok (penv, env, T.Intr_boundary b')
    | Intr_datagroup ds ->
      error_out "User-defined datagroups not supported\n" elt.loc
    | Intr_formula nf ->
      let* nf' = tc_named_formula env nf in
      let nf_ty = ity_of_named_formula env nf.elt in
      let new_env = add_to_ctxt env nf.elt.formula_name nf_ty in
      ok (penv, new_env, T.Intr_formula nf')
    | Intr_inductive ind ->
      let* ind' = tc_inductive_predicate env ind in
      let ind_ty = ity_of_inductive_predicate env ind.elt in
      let new_env = add_to_ctxt env ind.elt.ind_name ind_ty in
      ok (penv, new_env, T.Intr_inductive ind')
    | Intr_import import ->
      let* () = wf_import elt.loc import.elt in
      tc_interface_import penv env intr_name import
    | Intr_extern edecl ->
      let* new_env, edecl' = tc_extern env edecl in
      ok (penv, new_env, T.Intr_extern edecl') in
  match M.find intr_name penv with
  | Typed (_, T.Unary_interface idecl', Unary idecl'_env) ->
    ok (penv, idecl'_env, idecl')
  | _ ->
    let* penv, env, elts =
      List.fold_left (fun acc elt ->
          let* penv, env, elts = acc in
          let* penv', env', elt' = walk penv env elt in
          ok (penv', env', elt' :: elts)
        ) (ok (penv, tenv, [])) intr_def.elt.intr_elts in
    let annot_idef = T.{intr_name = intr_name; intr_elts = List.rev elts} in
    let penv = update_tpenv_unary penv intr_name
        (Unr_intr intr_def)
        (T.Unary_interface annot_idef)
        env in
    ok (penv, env, annot_idef)

(* tc_interface_import P G iname import = J

   Invariant:
   Let I be the name of the interface imported in the import declaration import.
   If P, G |- import then J = ok (P', G', import')

   where P' contains I |-> Typed (Annot(P[I]), TypeEnv(P[I]))

   and G' = G U G1 U ... U Gn where each Gi is the typing environment of
   interface i, possibly transitively imported, and can contain qualified
   identifiers.

   Further, for each interface J in P[iname]'s scope,
   P contains J |-> Typed (Annot(P[J]), TypeEnv(P[J]))

   import' is an annotated variant of import.
*)
and tc_interface_import penv env intr_name import_decl
  : (tpenv * tenv * T.interface_elt, string) result =
  let open Printf in
  let loc = import_decl.loc in
  let {import_kind=kind; import_name=import; related_by} = import_decl.elt in
  let import_as = import_decl.elt.import_as in
  let* () = wf_ident loc import in
  let iname = string_of_ident import in
  let annot_import_decl = T.mk_import kind import related_by in
  match kind with
  | Itheory -> ok (penv, env, T.Intr_import annot_import_decl)
  | Iregular ->
    match M.find import penv with
    | Typed (_, T.Unary_interface idecl', Unary env') ->
      let comb_env = tenv_union_qualified env env' import_as in
      ok (penv, comb_env, T.Intr_import annot_import_decl)
    | Untyped (Unr_intr idecl' as intr_prog) ->
      assert (string_of_ident idecl'.elt.intr_name = iname);
      if interface_does_import idecl' intr_name then
        let msg = sprintf "Recursive imports between %s and %s not allowed" in
        error_out (msg iname (string_of_ident intr_name)) loc
      else
        let* penv', env', idecl' =
          tc_interface penv {initial_tenv with ctbl=env.ctbl} idecl' in
        let idecl' = T.Unary_interface idecl' in
        let penv' = update_tpenv_unary penv import intr_prog idecl' env' in
        let comb_env = tenv_union_qualified env env' import_as in
        ok (penv', comb_env, T.Intr_import annot_import_decl)
    | _ | exception Not_found ->
      error_out (Printf.sprintf "Unknown interface %s" iname) loc

let wf_module_annotations mdl_def =
  let open Printf in
  let name,loc = string_of_ident mdl_def.elt.mdl_name, mdl_def.loc in
  let intr_name = string_of_ident mdl_def.elt.mdl_interface in
  let no_public_check nf = match nf.elt.annotation with
    | Some Private_invariant | None -> ok ()
    | Some Public_invariant ->
      let msg = sprintf "Public invariant %s must be defined in interface %s" in
      error_out (msg (string_of_ident nf.elt.formula_name) intr_name) loc in
  let preds = module_predicates mdl_def in
  let* _ = sequence (List.map no_public_check preds) in
  let priv = filter (fun e -> e.elt.annotation = Some Private_invariant) preds in
  if length priv <= 1 then ok () else
  error_out (sprintf "Module %s can only have one private invariant" name) loc

(* Type checks module.  Requires that the module is well-founded,
   respects its ascribed interface, and the environment contains all
   required definitions. *)
let rec tc_module penv env mdl_def
  : (tpenv * tenv * T.module_def, string) result =
  let mdl_name = mdl_def.elt.mdl_name in
  let* () = wf_module_annotations mdl_def in
  let interface_env penv loc intr_name =
    match M.find intr_name penv with
    | Typed (Unr_intr idef, Unary_interface _, Unary env) ->
      ok (penv, idef, env)
    | Untyped (Unr_intr idef) ->
      let* penv, env, _ =
        tc_interface penv {initial_tenv with ctbl=env.ctbl} idef in
      ok (penv, idef, env)
    | _
    | exception Not_found ->
      error_out (
        Printf.sprintf "Unknown interface %s"
          (string_of_ident intr_name)
      ) loc in
  let walk penv env elt : (tpenv * tenv * T.module_elt, string) result =
    match elt.elt with
    | Mdl_cdef {elt=Class cdecl; _} ->
      let* cdecl' = tc_cdecl env cdecl in
      let ctbl = Ctbl.add env.ctbl cdecl' in
      let new_env = {env with ctbl} in
      let cdef = T.Class cdecl' in
      ok (penv, new_env, T.Mdl_cdef cdef)
    | Mdl_mdef ({elt=Method (mdecl, com); loc} as mdef) ->
      let* _ = tc_meth_decl env mdecl in
      let meth_ty = ity_of_meth_decl env mdecl.elt in
      let new_env = add_to_ctxt env mdecl.elt.meth_name meth_ty in
      let* mdef' = tc_meth_def new_env mdef in
      ok (penv, new_env, T.Mdl_mdef mdef')
    | Mdl_vdecl (m, id, ty) ->
      let* () = wf_vdecl env m id ty in
      begin match m with
        | Modscope ->
          let id_ty = ity_of_ty env ty.elt in
          let new_env = add_to_ctxt env id id_ty in
          ok (penv, new_env, T.Mdl_vdecl (m, id -: id_ty, id_ty))
        | _ -> error_out (
            Printf.sprintf "Expected %s to be modscope"
              (string_of_ident id)
          ) elt.loc
      end
    | Mdl_datagroup (grp, flds) ->
      error_out "User-defined datagroups not supported\n" elt.loc
    | Mdl_formula nf ->
      let* nf' = tc_named_formula env nf in
      let form_ty = ity_of_named_formula env nf.elt in
      let new_env = add_to_ctxt env nf.elt.formula_name form_ty in
      ok (penv, new_env, T.Mdl_formula nf')
    | Mdl_inductive ind ->
      let* ind' = tc_inductive_predicate env ind in
      let ind_ty = ity_of_inductive_predicate env ind.elt in
      let new_env = add_to_ctxt env ind.elt.ind_name ind_ty in
      ok (penv, new_env, T.Mdl_inductive ind')
    | Mdl_import idecl ->
      let* () = wf_import elt.loc idecl.elt in
      tc_module_import penv env mdl_name idecl
    | Mdl_extern edecl ->
      let* new_env, edecl' = tc_extern env edecl in
      ok (penv, new_env, T.Mdl_extern edecl') in
  let interface_name = mdl_def.elt.mdl_interface in
  let* penv, idef, inienv = interface_env penv mdl_def.loc interface_name in
  let inienv = tenv_union inienv env in
  match M.find mdl_name penv with
  | Typed (Unr_mdl _, T.Unary_module mdl', Unary mdl'_env) ->
    ok (penv, mdl'_env, mdl')
  | _ ->
    let* () = wf_interface_module inienv idef mdl_def in
    let* penv, env, elts =
      List.fold_left (fun acc elt ->
          let* penv, env, elts = acc in
          let* penv', env', elt' = walk penv env elt in
          ok (penv', env', elt' :: elts)
        ) (ok (penv, inienv, [])) mdl_def.elt.mdl_elts in
    let annot_mdef =
      T.{mdl_name = mdl_name;
         mdl_interface = interface_name;
         mdl_elts = elts} in
    let penv = update_tpenv_unary penv mdl_name
        (Unr_mdl mdl_def)
        (T.Unary_module annot_mdef)
        env in
    ok (penv, env, annot_mdef)

and tc_datagroup_def env grp loc flds : (ident T.t list, string) result =
  match flds with
  | [] -> ok []
  | f :: flds ->
    match Ctbl.field_type env.ctbl ~field:f with
    | Some ty ->
      let* flds' = tc_datagroup_def env grp loc flds in
      ok (f -: ty :: flds')
    | None ->
      error_out (
        Printf.sprintf "Unknown field %s in datagroup %s"
          (string_of_ident f) (string_of_ident grp)
      ) loc

and tc_module_import penv env mdl_name import
  : (tpenv * tenv * T.module_elt, string) result =
  let {elt={import_kind; import_name; import_as; related_by}; loc} = import in
  let* () = wf_ident loc import_name in
  let* () = wf_ident_opt loc import_as in
  let iname = string_of_ident import_name in
  let annot_import =
    let decl = T.{import_kind; import_name; import_as; related_by} in
    T.Mdl_import decl in
  match import_kind with
  | Itheory -> ok (penv, env, annot_import)
  | Iregular ->
    match M.find import_name penv with
    | Typed (Unr_mdl mdl', T.Unary_module _, Unary env') ->
      let combined_env = tenv_union_qualified env env' import_as in
      ok (penv, combined_env, annot_import)
    | Typed (Unr_intr intr', T.Unary_interface _, Unary env') ->
      let combined_env = tenv_union_qualified env env' import_as in
      ok (penv, combined_env, annot_import)
    | Untyped (Unr_mdl mdl') ->
      if module_does_import mdl' mdl_name
      then
        (* FIXME: Checked initially when computing dependencies between modules;
           this path may be unreachable. *)
        error_out (
          Printf.sprintf "Mutually recursive imports between %s and %s \
                          not supported"
            (string_of_ident mdl'.elt.mdl_name)
            (string_of_ident mdl_name)
        ) loc
      else
        let* penv, env', _ =
          tc_module penv {initial_tenv with ctbl=env.ctbl} mdl' in
        let combined_env = tenv_union_qualified env env' import_as in
        ok (penv, combined_env, annot_import)
    | _ | exception Not_found ->
      error_out (Printf.sprintf "Unknown module or interface %s" iname) loc


(* -------------------------------------------------------------------------- *)
(* Type checking (relation formulas and biprograms)                           *)
(* -------------------------------------------------------------------------- *)

let rec tc_value_in_state (env: bi_tenv) (v: value_in_state node)
  : (T.value_in_state T.t * ity, string) result =
  match v.elt with
  | Left e ->
    let* e', e_ty = tc_exp env.left_tenv e in
    ok (T.Left e' -: e_ty, e_ty)
  | Right e ->
    let* e', e_ty = tc_exp env.right_tenv e in
    ok (T.Right e' -: e_ty, e_ty)

let rec tc_biexp (env: bi_tenv) (bexp: biexp node)
  : (T.biexp T.t * ity, string) result =
  match bexp.elt with
  | Bibinop (op, e1, e2) ->
    let* e1', e1_ty = tc_biexp env e1 in
    let* e2', e2_ty = tc_biexp env e2 in
    begin match op with
      | Equal | Nequal ->
        let* () = match e1_ty with
          | Tint | Tbool | Trgn | Tunit | Tclass _
          | Tanyclass | Tmath _ -> ok ()
          | _ -> error_out "Cannot use = to compare non-values" e1.loc in
        let* () = expect_tys [e2.loc, e2_ty, e1_ty; e1.loc, e1_ty, e2_ty] in
        ok (T.Bibinop (op, e1', e2') -: T.Tbool, T.Tbool)
      | _ ->
        let p1_ty, p2_ty, ret_ty = binop_ty op in
        let* () = expect_tys [e2.loc, e2_ty, p2_ty; e1.loc, e1_ty, p1_ty] in
        ok (T.Bibinop (op, e1', e2') -: ret_ty, ret_ty)
    end
  | Bivalue v ->
    let* v', v_ty = tc_value_in_state env v in
    ok (T.Bivalue v' -: v_ty, v_ty)
  | Biconst ce ->
    let ce', ce_ty = tc_const_exp ce in ok (T.Biconst ce' -: ce_ty, ce_ty)

let rec tc_rformula (env: bi_tenv) (rf: rformula node)
  : (T.rformula, string) result =
  let open List in
  let { left_tenv = lenv; right_tenv = renv; _ } = env in
  match rf.elt with
  | Rprimitive (pred, args) -> tc_rformula_prim env rf.loc pred args
  | Rbiexp bexp ->
    let* bexp', bexp_ty = tc_biexp env bexp in
    let* () = expect_ty bexp.loc bexp_ty T.Tbool in
    ok (T.Rbiexp bexp')
  | Rnot rf -> 
    let* rf' = tc_rformula env rf in
    ok (T.Rnot rf')
  | Rconn (c, rf1, rf2) ->
    let* rf1' = tc_rformula env rf1 in
    let* rf2' = tc_rformula env rf2 in
    ok (T.Rconn (c, rf1', rf2'))
  | Rquant (q, (lbinds, rbinds), rfrm) ->
    let* lenv, lbinds = add_quantifier_bindings lenv lbinds in
    let* renv, rbinds = add_quantifier_bindings renv rbinds in
    let env = { env with left_tenv = lenv; right_tenv = renv } in
    let* rfrm' = tc_rformula env rfrm in
    ok (T.Rquant (q, (lbinds, rbinds), rfrm'))
  | Rlet (lvar, rvar, rfrm) ->
    let tc_let_var env decl = match decl with
      | Some (vid, vtyopt, vbind) ->
        let* () = wf_ident rf.loc vid in
        let {value = let_valu; _} = vbind.elt in
        let* valu', lty = tc_let_bound_value env vbind.loc let_valu vtyopt in
        let env' = add_to_ctxt env vid lty in
        let is_old = vbind.elt.is_old and is_init = vbind.elt.is_init in
        assert (not (is_old && is_init));
        let binder = T.{value = valu'; is_old; is_init} in
        ok (env', Some (vid -: lty, lty, binder -: lty))
      | None -> ok (env, None) in
    let* (lenv, lvar') = tc_let_var env.left_tenv lvar in
    let* (renv, rvar') = tc_let_var env.right_tenv rvar in
    let env' = {env with left_tenv = lenv; right_tenv = renv} in
    let* rfrm' = tc_rformula env' rfrm in
    ok (T.Rlet (lvar', rvar', rfrm'))
  | Ragree (g, f) ->
    let* lg', lg_ty = tc_exp lenv g in
    let* rg', rg_ty = tc_exp renv g in
    let* () = expect_tys [g.loc, lg_ty, Trgn; g.loc, rg_ty, Trgn] in
    begin match Ctbl.field_type lenv.ctbl ~field:f,
                Ctbl.field_type renv.ctbl ~field:f with
      | Some lf_ty, Some rf_ty ->
        let* () = expect_tys [g.loc, lf_ty, rf_ty; g.loc, rf_ty, lf_ty] in
        ok (T.Ragree (lg', f -: lf_ty))
      | None, None ->
        if is_datagroup f && is_datagroup f
        then ok (T.Ragree (lg', f -: Tdatagroup))
        else error_out "Invalid agreement\n" rf.loc
      | _, _ -> error_out (
          Printf.sprintf
            "Invalid agreement: field mismatch between sides: %s"
            (string_of_ident f)
        ) rf.loc
    end
  | Rbiequal (e1, e2) ->
    let* e1', e1_ty = tc_exp lenv e1 in
    let* e2', e2_ty = tc_exp renv e2 in
    let* () = match e1_ty with
      | Tint | Tbool | Tunit | Trgn | Tclass _ | Tanyclass | Tmath _ -> ok ()
      | Tfunc _ | Tmeth _ | Tdatagroup | Tprop ->
        error_out "Cannot use =:= to compare non-values" e1.loc in
    let* () = expect_tys [e1.loc, e1_ty, e2_ty; e2.loc, e2_ty, e1_ty] in
    ok (T.Rbiequal (e1', e2'))
  | Rleft f  -> let* f' = tc_formula lenv f in ok (T.Rleft  f')
  | Rright f -> let* f' = tc_formula renv f in ok (T.Rright f')
  | Rboth f  ->
    let* fl = tc_formula lenv f in
    let* fr = tc_formula renv f in
    ok (T.Rboth fr)

and tc_rformula_prim env loc pred args : (T.rformula, string) result =
  let open List in
  let spread ((loc,ty),param_ty) = (loc,ty,param_ty) in
  let { left_tenv = lenv; right_tenv = renv; _ } = env in
  match M.find pred env.bipreds with
  | lparams, rparams ->
    let args  = get_elts args in
    let largs = filter_map (function Left e  -> Some e | _ -> None) args in
    let rargs = filter_map (function Right e -> Some e | _ -> None) args in
    let llen, rlen   = length largs, length rargs in
    let lplen, rplen = length lparams, length rparams in
    if lplen <> llen || rplen <> rlen
    then error_out
        (Printf.sprintf
           "%s expected %d | %d arguments but got %d | %d arguments"
           (string_of_ident pred)
           lplen rplen
           llen rlen)
        loc
    else
      let* largs_check = sequence (map (tc_exp lenv) largs) in
      let* rargs_check = sequence (map (tc_exp renv) rargs) in
      let largs', largs_ty = split largs_check in
      let rargs', rargs_ty = split rargs_check in
      let largs_ty_locs    = combine (map (fun e -> e.loc) largs) largs_ty in
      let rargs_ty_locs    = combine (map (fun e -> e.loc) rargs) rargs_ty in
      let lcheck = map spread (combine largs_ty_locs lparams) in
      let rcheck = map spread (combine rargs_ty_locs rparams) in
      let* ()    = expect_tys (lcheck @ rcheck) in
      ok (T.Rprimitive {name=pred; left_args=largs'; right_args=rargs'})
  | exception Not_found ->
    let msg = "Unknown bipredicate " ^ (string_of_ident pred) in
    error_out msg loc

let rec tc_bicommand env cc : (T.bicommand, string) result =
  let { left_tenv = lenv; right_tenv = renv; _ } = env in
  match cc.elt with
  | Bihavoc_right (x, r) ->
    if !all_exists_mode then
      let* () = wf_ident cc.loc x in
      let* x_ty = find_in_ctxt env.right_tenv x cc.loc in
      let* rfrm = tc_rformula env r in
      ok (T.Bihavoc_right (x -: x_ty, rfrm))
    else
      let msg = "HavocR only allowed when -all-exists is set" in
      error_out msg cc.loc
  | Bisplit (lc, rc) ->
    let* lc' = tc_command lenv lc in
    let* rc' = tc_command renv rc in
    ok (T.Bisplit (lc', rc'))
  | Bisync ac ->
    let* ac' = tc_atomic_command lenv ac in
    let* ac' = tc_atomic_command renv ac in
    ok (T.Bisync ac')
  | Bivardecl (ldecl, rdecl, c) ->
    let tc_vdecl env decl = match decl with
      | Some (vid, vmod, vty) ->
        let* () = wf_ident cc.loc vid in
        let* () = ensure_type_is_known env vty in
        let vty = ity_of_ty env vty.elt in
        let env = add_to_ctxt env vid vty in
        ok (env, Some (vid -: vty, vmod, vty))
      | None -> ok (env, None) in
    let* (lenv, ldecl) = tc_vdecl lenv ldecl in
    let* (renv, rdecl) = tc_vdecl renv rdecl in
    let env' = {env with left_tenv = lenv; right_tenv = renv} in
    let* c' = tc_bicommand env' c in
    ok (T.Bivardecl (ldecl, rdecl, c'))
  | Biseq (bc1, bc2) ->
    let* bc1' = tc_bicommand env bc1 in
    let* bc2' = tc_bicommand env bc2 in
    ok (T.Biseq (bc1', bc2'))
  | Biif (lguard, rguard, conseq, alter) ->
    let* lguard', lguard_ty = tc_exp lenv lguard in
    let* rguard', rguard_ty = tc_exp renv rguard in
    let* () = expect_tys [
        lguard.loc, lguard_ty, Tbool;
        rguard.loc, rguard_ty, Tbool
      ] in
    let* conseq' = tc_bicommand env conseq in
    let* alter' = tc_bicommand env alter in
    ok (T.Biif (lguard', rguard', conseq', alter'))
  | Biif4 (lguard, rguard, tt, tf, ft, ff) ->
    let* lguard', lguard_ty = tc_exp lenv lguard in
    let* rguard', rguard_ty = tc_exp renv rguard in
    let* () = expect_tys [
        lguard.loc, lguard_ty, Tbool;
        rguard.loc, rguard_ty, Tbool
      ] in
    let* then_then = tc_bicommand env tt in
    let* then_else = tc_bicommand env tf in
    let* else_then = tc_bicommand env ft in
    let* else_else = tc_bicommand env ff in
    let left = T.projl_simplify in
    let right = T.projr_simplify in
    let* () =
      (* TODO: Use Result monad *)
      assert (T.eqv_command (left then_then) (left then_else));
      assert (T.eqv_command (left else_then) (left else_else));
      assert (T.eqv_command (right then_then) (right else_then));
      assert (T.eqv_command (right then_else) (right else_else));
      ok ()
    in
    ok (T.Biif4 (lguard', rguard', {then_then;then_else;else_then;else_else}))
  | Biwhile (lguard, rguard, align, bwspec, body) ->
    let* lguard', lguard_ty = tc_exp lenv lguard in
    let* rguard', rguard_ty = tc_exp renv rguard in
    let* () = expect_tys [
        lguard.loc, lguard_ty, Tbool;
        rguard.loc, rguard_ty, Tbool
      ] in
    let* bwspec = tc_biwhile_spec env bwspec in
    let* body' = tc_bicommand env body in
    begin match align with
      | None ->
        let false_rfrm = T.Rleft (T.Ffalse), T.Rright (T.Ffalse) in
        ok (T.Biwhile (lguard', rguard', false_rfrm, bwspec, body'))
      | Some (lf, rf) ->
        let* lf' = tc_rformula env lf in
        let* rf' = tc_rformula env rf in
        ok (T.Biwhile (lguard', rguard', (lf', rf'), bwspec, body'))
    end
  | Biassert rf ->
    let* rf' = tc_rformula env rf in
    ok (T.Biassert rf')
  | Biassume rf ->
    let* rf' = tc_rformula env rf in
    ok (T.Biassume rf')
  | Biupdate (lid, rid) ->
    let* lid_ty = find_in_ctxt lenv lid cc.loc in
    let* rid_ty = find_in_ctxt renv rid cc.loc in
    let* () = expect_ty_pred cc.loc lid_ty is_class_ty
        (Printf.sprintf "Expected %s to be of class type"
           (string_of_ident lid)) in
    let* () = expect_ty cc.loc rid_ty lid_ty in
    ok (T.Biupdate (lid -: lid_ty, rid -: rid_ty))

and tc_biwhile_spec env bws : (T.biwhile_spec, string) result =
  let rec check invs (effl, effr) v = function
    | [] -> ok (invs, (effl, effr), v)
    | {elt = Biwvariant b} :: rest ->
      let* b, _ = tc_biexp env b in check  invs (effl, effr) (Some b) rest
    | {elt = Biwinvariant rf} :: rest ->
      let* rf = tc_rformula env rf in check (rf :: invs) (effl, effr) v rest
    | {elt = Biwframe (e, e')} :: rest ->
      let* e = tc_effect env.left_tenv e in
      let* e' = tc_effect env.right_tenv e' in
      check invs (e @ effl, e' @ effr) v rest in
  let* invs, (effl, effr), v = check [] ([], []) None bws in
  ok (T.{biwinvariants = rev invs; biwframe = effl, effr; biwvariant = v})

let wf_coupling_params loc nf : (unit,string) result =
  let open Printf in
  if nf.is_coupling && nf.biparams <> ([],[])
  then
    let msg = sprintf "coupling relation %s cannot have parameters\n" in
    error_out (msg (string_of_ident nf.biformula_name)) loc
  else ok ()

let tc_binamed_formula bienv nf : (bi_tenv * T.named_rformula, string) result =
  let open List in
  let* () = wf_ident nf.loc nf.elt.biformula_name in
  let {left_tenv = lenv; right_tenv = renv; _} = bienv in
  match nf.elt.kind with
  | `Axiom | `Lemma ->
    let* rfrm = tc_rformula bienv nf.elt.body in
    let named = T.{kind = nf.elt.kind;
                   biformula_name = nf.elt.biformula_name;
                   biparams = ([],[]);
                   is_coupling = nf.elt.is_coupling;
                   body = rfrm} in
    ok (bienv, named)
  | `Predicate ->
    let lparams, rparams = map_pair (map snd) nf.elt.biparams in
    let lparam_names, rparam_names =
      let f = map (fun p -> (snd p).loc, fst p) in
      map_pair f nf.elt.biparams in
    let* () = wf_coupling_params nf.loc nf.elt in
    let* _   = sequence (map (uncurry wf_ident) lparam_names) in
    let* _   = sequence (map (uncurry wf_ident) rparam_names) in
    let* _   = sequence (map (ensure_type_is_known lenv) lparams) in
    let ltys = map (ity_of_ty lenv) (get_elts lparams) in
    let rtys = map (ity_of_ty renv) (get_elts rparams) in
    let lps  = combine (map snd lparam_names) ltys in
    let rps  = combine (map snd rparam_names) rtys in
    let lenv = fold_right (fun (n,t) e -> add_to_ctxt e n t) lps lenv in
    let renv = fold_right (fun (n,t) e -> add_to_ctxt e n t) rps renv in
    let bprds = M.add nf.elt.biformula_name (ltys,rtys) bienv.bipreds in
    let bienv = { bienv with bipreds=bprds } in
    let bienv' = { bienv with left_tenv=lenv; right_tenv=renv} in
    let* rfrm = tc_rformula bienv' nf.elt.body in
    let lprms = map (fun (i,t) -> i -: t, t) lps in
    let rprms = map (fun (i,t) -> i -: t, t) rps in
    let named = T.{kind = nf.elt.kind;
                   biformula_name = nf.elt.biformula_name;
                   biparams = (lprms, rprms);
                   is_coupling = nf.elt.is_coupling;
                   body = rfrm } in
    ok (bienv, named)

let add_named_rformula (env: bi_tenv) (nf: named_rformula node) (* FIXME: UNUSED *)
  : (bi_tenv, string) result =
  let open List in
  let {left_tenv = lenv; right_tenv = renv; _} = env in
  let* () = wf_ident nf.loc nf.elt.biformula_name in
  match nf.elt.kind with
  | `Axiom | `Lemma -> ok env
  | `Predicate ->
    let (lparams, rparams) = map_pair (map snd) nf.elt.biparams in
    let (lparam_names, rparam_names) =
      map_pair (map (fun p -> (snd p).loc, fst p)) nf.elt.biparams in
    let* _ = sequence (map (uncurry wf_ident) lparam_names) in
    let* _ = sequence (map (uncurry wf_ident) rparam_names) in
    let* _ = sequence (map (ensure_type_is_known lenv) lparams) in
    let* _ = sequence (map (ensure_type_is_known renv) rparams) in
    let ltys = map (ity_of_ty lenv) @@ get_elts lparams in
    let rtys = map (ity_of_ty renv) @@ get_elts rparams in
    let bipreds = M.add nf.elt.biformula_name (ltys, rtys) env.bipreds in
    ok { env with bipreds }

let rec tc_bispec env spec : (T.bispec, string) result =
  match spec.elt with
  | [] -> ok []
  | {elt; loc} :: spec ->
    let* ss' = tc_bispec env {elt=spec; loc} in
    match elt with
    | Biprecond f ->
      let* f' = tc_rformula env f in
      ok (T.Biprecond f' :: ss')
    | Bipostcond f ->
      let* f' = tc_rformula env f in
      ok (T.Bipostcond f' :: ss')
    | Bieffects (les, res) ->
      let* les' = tc_effect env.left_tenv les in
      let* res' = tc_effect env.right_tenv res in
      ok (T.Bieffects (les', res') :: ss')

let tc_bimeth_decl (env: bi_tenv) (mdecl: bimeth_decl node)
  : (bi_tenv * T.bimeth_decl, string) result =
  let open List in
  let add_params env params : (tenv * T.meth_param_info list, string) result =
    fold_right (fun ({param_name; param_ty={elt = ty; loc}; _} as p) acc ->
        let* env, params = acc in
        let* () = wf_ident loc param_name in
        let* () = ensure_type_is_known env p.param_ty in
        let ty' = ity_of_ty env ty in
        let env = add_to_ctxt env param_name ty' in
        let prm = T.{param_name = param_name -: ty';
                     param_modifier = p.param_modifier;
                     param_ty = ty';
                     is_non_null = p.is_non_null} in
        ok (env, prm :: params)
      ) params (ok (env, []))
  in
  let* () = wf_ident mdecl.loc mdecl.elt.bimeth_name in
  let {left_tenv = lenv; right_tenv = renv; _} = env in
  let lparams = mdecl.elt.bimeth_left_params in
  let rparams = mdecl.elt.bimeth_right_params in
  let lres, rres = mdecl.elt.result_ty in
  let lres_ty = ity_of_ty lenv lres.elt in
  let rres_ty = ity_of_ty renv rres.elt in
  let* () = ensure_type_is_known lenv lres in
  let* () = ensure_type_is_known renv rres in
  let* lenv, lparams' = add_params lenv lparams in
  let* renv, rparams' = add_params renv rparams in
  let lenv = add_to_ctxt lenv (Id "result") lres_ty in
  let renv = add_to_ctxt renv (Id "result") rres_ty in
  let env  = {env with left_tenv = lenv; right_tenv = renv} in
  let* bimeth_spec = tc_bispec env mdecl.elt.bimeth_spec in
  let lres_non_null = is_class_ty lres_ty && fst mdecl.elt.result_is_non_null in
  let rres_non_null = is_class_ty rres_ty && snd mdecl.elt.result_is_non_null in
  let bimeth_decl =
    T.{bimeth_name = mdecl.elt.bimeth_name;
       bimeth_left_params = lparams';
       bimeth_right_params = rparams';
       result_ty = (lres_ty, rres_ty);
       result_is_non_null = (lres_non_null, rres_non_null);
       bimeth_can_diverge = false;
       bimeth_spec} in
  ok (env, bimeth_decl)

let rec tc_bimeth_def (env: bi_tenv) (mdef: bimeth_def node)
  : (T.bimeth_def, string) result =
  let Bimethod (bimdecl, ccopt) = mdef.elt in
  let* meth_env, bimdecl' = tc_bimeth_decl env bimdecl in
  match ccopt with
  | Some cc ->
    let* cc' = tc_bicommand meth_env cc in
    if !tc_debug then begin
      let fmt = Format.err_formatter in
      Printf.fprintf stderr "Left projection simplfied:\n";
      Pretty.pp_command fmt (T.projl_simplify cc');
      Format.pp_print_newline fmt ();
      Format.pp_print_newline fmt ();
      Format.pp_print_flush fmt ();
      Printf.fprintf stderr "Right projection simplified:\n";
      Pretty.pp_command fmt (T.projr_simplify cc');
      Format.pp_print_newline fmt ();
      Format.pp_print_newline fmt ();
      Format.pp_print_flush fmt ();
    end;
    ok (T.Bimethod (bimdecl', Some cc'))
  | None -> ok (T.Bimethod (bimdecl', None))


let wf_bimeth_def loc penv lmdl rmdl bimdef : (unit,string) result =
  let open T in

  let Bimethod (bimdecl,cc) = bimdef in
  let meth_name = bimdecl.bimeth_name in
  let mname_str = string_of_ident meth_name in

  let check c1 c2 side =
    if eqv_command c1 (rw_command c2) then ok ()
    else error_out (
        Printf.sprintf "Malformed bicommand (%s): %s" side mname_str
      ) loc in

  let check_opt c1 c2 side = match c2 with
    | None -> ok ()
    | Some c2 -> check c1 c2 side in

  let get_unary_method_body mdl_name name =
    match M.find mdl_name penv with
    | Typed (_, Unary_module mdl, _) ->
      let sel_fn = function
        | Mdl_mdef (Method (m, Some c)) when m.meth_name.node = name -> Some c
        | _ -> None in
      begin match List.filter_map sel_fn mdl.mdl_elts with
        | [] -> None
        | ms -> Some (last ms)
      end
    | Untyped _ -> assert false
    | _ | exception Not_found -> assert false in

  if Option.is_none cc then ok () else begin
    let cc = Option.get cc in
    let meth_name = bimdecl.bimeth_name in
    let lmeth_com = get_unary_method_body lmdl meth_name in
    let rmeth_com = get_unary_method_body rmdl meth_name in
    let ccl = projl_simplify cc and ccr = projr_simplify cc in
    let* () = check_opt ccl lmeth_com "left" in
    let* () = check_opt ccr rmeth_com "right" in
    ok ()
  end


let ensure_module_exists penv loc mdl =
  if M.exists (fun k _ -> k = mdl) penv then ok ()
  else error_out ("Unknown module " ^ (string_of_ident mdl)) loc

let ensure_single_coupling_annotation bimdl_def : (unit, string) result =
  let open Printf in
  let name = string_of_ident bimdl_def.bimdl_name in
  let msg = sprintf "Expected %s to have a single coupling annotation\n" name in
  let cs = ref 0 in
  let last_loc = ref None in
  List.iter (fun e -> match e.elt with
      | Bimdl_formula {elt = {is_coupling = true; _}; loc} ->
        incr cs; last_loc := Some loc;
      | _ -> ()
    ) bimdl_def.bimdl_elts;
  if !cs <= 1 then ok () else error_out msg (Option.get !last_loc)

let rec tc_bimodule (penv: tpenv) (env: bi_tenv) (bimdl_def: bimodule_def node)
  : (tpenv * bi_tenv * T.bimodule_def, string) result =
  let left_mdl  = bimdl_def.elt.bimdl_left_impl in
  let right_mdl = bimdl_def.elt.bimdl_right_impl in
  let biname = bimdl_def.elt.bimdl_name in
  let walk penv env elt : (tpenv * bi_tenv * T.bimodule_elt, string) result =
    match elt.elt with
    | Bimdl_formula nf ->
      let* env, nf' = tc_binamed_formula env nf in
      ok (penv, env, T.Bimdl_formula nf')
    | Bimdl_mdef mdef ->
      let Bimethod (mdecl, _) = mdef.elt in
      let* mdef' = tc_bimeth_def env mdef in
      let env = add_bimethod env mdef' in
      let* () = wf_bimeth_def elt.loc penv left_mdl right_mdl mdef' in
      ok (penv, env, T.Bimdl_mdef mdef')
    | Bimdl_extern ex -> tc_bimodule_extern penv env ex
    | Bimdl_import idecl ->
      let* () = wf_import elt.loc idecl.elt in
      tc_bimodule_import penv env biname idecl in
  let* () = ensure_module_exists penv bimdl_def.loc left_mdl in
  let* () = ensure_module_exists penv bimdl_def.loc right_mdl in
  let* () = ensure_single_coupling_annotation bimdl_def.elt in
  match M.find biname penv with
  | Typed (Rel_mdl _, T.Relation_module bimdl', Relational bimdl'_env) ->
    ok (penv, bimdl'_env, bimdl')
  | _ ->
    let* inienv = tc_bimodule_inienv penv env left_mdl right_mdl biname in
    let* penv, env, elts =
      List.fold_left (fun acc elt ->
          let* penv, env, elts = acc in
          let* penv', env', elt' = walk penv env elt in
          ok (penv', env', elt' :: elts)
        ) (ok (penv, inienv, [])) bimdl_def.elt.bimdl_elts in
    let annot_bimdl_def =
      T.{bimdl_name = biname;
         bimdl_left_impl = left_mdl;
         bimdl_right_impl = right_mdl;
         bimdl_elts = rev elts} in
    let astfrag = Rel_mdl bimdl_def in
    let pfrag = T.Relation_module annot_bimdl_def in
    let penv = update_tpenv_relational penv biname astfrag pfrag env in
    ok (penv, env, annot_bimdl_def)

and tc_bimodule_extern penv env extern
    : (tpenv * bi_tenv * T.bimodule_elt, string) result =
  match extern.elt.extern_kind with
  | Ex_bipredicate ->
     let name = extern.elt.extern_symbol in
     let* () = wf_ident extern.loc name in
     let lparams,rparams = map_pair get_elts extern.elt.extern_biinput in
     let lparams = List.map (ity_of_ty env.left_tenv) lparams in
     let rparams = List.map (ity_of_ty env.right_tenv) rparams in
     let bipreds = M.add name (lparams, rparams) env.bipreds in
     let env' = {env with bipreds} in
     let extern' = T.Extern_bipredicate {name; lparams; rparams} in
     ok (penv, env', T.Bimdl_extern extern')
  | _ ->
     let* left_tenv, _ = tc_extern env.left_tenv extern in
     let* right_tenv, ex' = tc_extern env.right_tenv extern in
     let env = {env with left_tenv; right_tenv} in
     ok (penv, env, T.Bimdl_extern ex')

and tc_bimodule_import penv env bimdl_name import
  : (tpenv * bi_tenv * T.bimodule_elt, string) result =
  let {elt={import_kind; import_name; import_as; related_by}; loc} = import in
  let* () = wf_ident loc import_name in
  let* () = wf_ident_opt loc import_as in
  let iname = string_of_ident import_name in
  let annot_import =
    let decl = T.{import_kind; import_name; import_as; related_by} in
    T.Bimdl_import decl in
  match import_kind with
  | Itheory -> ok (penv, env, annot_import)
  | Iregular ->
    match M.find import_name penv with
    | Typed (Rel_mdl mdl', T.Relation_module _, Relational env') ->
      let combined_env = bi_tenv_union env env' in
      ok (penv, combined_env, annot_import)
    | Untyped (Rel_mdl _) ->
      (* NOTE: In previous versions, the order in which modules would get type
         checked was not specified.  However, now we may rely on knowing that if
         M depends on N, then N is type checked before M.  Hence, we should
         never arrive at this case.
      *)
      assert false
    | _ | exception Not_found ->
      error_out (Printf.sprintf "Unknown bimodule %s" iname) loc

and add_bimethod env mdef =
  let open T in
  let Bimethod (mdecl, _) = mdef in
  let lparam_tys = List.map (fun e -> e.param_ty) mdecl.bimeth_left_params in
  let rparam_tys = List.map (fun e -> e.param_ty) mdecl.bimeth_right_params in
  let lmeth_ty = Tmeth { params = lparam_tys; ret = fst mdecl.result_ty } in
  let rmeth_ty = Tmeth { params = rparam_tys; ret = snd mdecl.result_ty } in
  let ltenv = add_to_ctxt env.left_tenv mdecl.bimeth_name lmeth_ty in
  let rtenv = add_to_ctxt env.right_tenv mdecl.bimeth_name rmeth_ty in
  {env with left_tenv=ltenv; right_tenv=rtenv}

and tc_bimodule_inienv penv env left_mdl right_mdl bimdl_name =
  let mk_import import_name =
    let import_kind, import_as, related_by = Iregular, None, None in
    no_loc {import_kind; import_name; import_as; related_by} in
  let limport = mk_import left_mdl and rimport = mk_import right_mdl in
  let lenv, renv = env.left_tenv, env.right_tenv in
  let* lpenv, lenv, _ = tc_module_import penv lenv bimdl_name limport in
  let* rpenv, renv, _ = tc_module_import lpenv renv bimdl_name rimport in
  let ctbl = Ctbl.union lenv.ctbl renv.ctbl in
  ok {env with left_tenv = {lenv with ctbl}; right_tenv = {renv with ctbl}}



(* -------------------------------------------------------------------------- *)
(* Uniqueness of names and misc. WF conditions                                *)
(* -------------------------------------------------------------------------- *)

(* Note: while the previous sections do define WF conditions, this
   section defines those that could potentially be turned off in a future
   revision. *)

let ensure_field_names_are_unique  = ref true
let ensure_class_names_are_unique  = ref true
let ensure_global_names_are_unique = ref true
let ensure_no_modscope_variables   = ref true

type known_names = {
  known_fields: ident M.t;
  known_classes: ident M.t;
  known_globals: ident M.t;
}

type known_map = {
  known_intr_names: known_names;
  known_mdl_names: known_names;
}

let empty_known_names = {
  known_fields = M.empty;
  known_classes = M.empty;
  known_globals = M.empty;
}

let empty_known_map = {
  known_intr_names = empty_known_names;
  known_mdl_names = empty_known_names;
}

let unique_field_names intr_name known cdecl : (known_names, string) result =
  let rec walk known = function
    | [] -> ok known
    | {elt = {field_name; _}; loc} :: flds ->
      if M.mem field_name known.known_fields
      then error_out
          (Printf.sprintf "Field %s has already been declared"
             (string_of_ident field_name))
          loc
      else
        let fields = M.add field_name intr_name known.known_fields in
        walk {known with known_fields = fields} flds in
  walk known cdecl.elt.fields

let unique_field_names_mdl mdl_intr_name known cdef
  : (known_names, string) result =
  let rec walk known = function
    | [] -> ok known
    | {elt = {field_name; _}; loc} :: flds ->
      if M.mem field_name known.known_fields
      then
        let intr_name = M.find field_name known.known_fields in
        if intr_name = mdl_intr_name
        then walk known flds
        else error_out
            (Printf.sprintf "Field %s has already been declared"
               (string_of_ident field_name))
            loc
      else
        let fields = M.add field_name mdl_intr_name known.known_fields in
        walk {known with known_fields = fields} flds in
  let Class cdecl = cdef.elt in
  walk known cdecl.elt.fields

let unique_class_names intr_name known cdecl : (known_names, string) result =
  let class_name = cdecl.elt.class_name in
  if M.mem class_name known.known_classes
  then error_out
      (Printf.sprintf "Class %s has already been declared"
         (string_of_ident class_name))
      cdecl.loc
  else
    let known_classes = M.add class_name intr_name known.known_classes in
    ok {known with known_classes}

let unique_class_names_mdl mdl_intr_name known cdef
  : (known_names, string) result =
  let Class cdecl = cdef.elt in
  let class_name = cdecl.elt.class_name in
  if M.mem class_name known.known_classes
  then
    let intr_name = M.find class_name known.known_classes in
    if intr_name = mdl_intr_name
    then ok known
    else error_out
        (Printf.sprintf "Class %s has already been declared"
           (string_of_ident class_name))
        cdecl.loc
  else
    let classes = M.add class_name mdl_intr_name known.known_classes in
    ok {known with known_classes = classes}

let check_unique_names_interface known idef : (known_map, string) result =
  let intr_name = idef.elt.intr_name in
  let rec walk known ielt =
    let* known = known in
    match ielt.elt with
    | Intr_cdecl cdecl ->
      begin match !ensure_class_names_are_unique,
                  !ensure_field_names_are_unique with
      | true, true ->
        let* known = unique_class_names intr_name known cdecl in
        let* known = unique_field_names intr_name known cdecl in
        ok known
      | false, true -> unique_field_names intr_name known cdecl
      | true, false -> unique_class_names intr_name known cdecl
      | _, _ -> ok known
      end
    | Intr_vdecl (modif, id, ty) ->
      if !ensure_global_names_are_unique
      && M.mem id known.known_globals
      then
        error_out (Printf.sprintf "Global %s has already been declared"
                     (string_of_ident id))
          ielt.loc
      else
        let globals = M.add id intr_name known.known_globals in
        ok {known with known_globals = globals}
    | _ -> ok known in
  let* known_intrs =
    List.fold_left walk (ok known.known_intr_names) idef.elt.intr_elts in
  ok {known with known_intr_names = known_intrs}

let check_unique_names_module known mdl : (known_map, string) result =
  let intr_name = mdl.elt.mdl_interface in
  let rec walk known melt =
    let* known = known in
    match melt.elt with
    | Mdl_cdef cdef ->
      begin match !ensure_class_names_are_unique,
                  !ensure_field_names_are_unique with
      | true, true ->
        let* known = unique_class_names_mdl intr_name known cdef in
        let* known = unique_field_names_mdl intr_name known cdef in
        ok known
      | false, true -> unique_field_names_mdl intr_name known cdef
      | true, false -> unique_class_names_mdl intr_name known cdef
      | false, false -> ok known
      end
    | Mdl_vdecl (Modscope, id, _) ->
      if !ensure_no_modscope_variables
      then error_out
          (Printf.sprintf
             "Cannot declare %s to be modscope: modscope variables \
              are currently not supported"
             (string_of_ident id))
          melt.loc
      else ok known
    | _ -> ok known in
  let* known_mdls =
    List.fold_left walk (ok known.known_mdl_names) mdl.elt.mdl_elts in
  ok {known with known_mdl_names = known_mdls}


(* -------------------------------------------------------------------------- *)
(* Array fields conditions                                                    *)
(* -------------------------------------------------------------------------- *)

(* In code, ensure there are no writes to Array.length and no reads or
   writes to Array.slots.  Additionally, in formulas ensure there is no
   points to predicate involving the slots field.

   EXCEPTION: can read/write .XLength or .XSlots in the constructor
*)
module Array_fields_wr_check : sig
  val check : T.program_elt * Ctbl.t -> unit
end = struct

  open T

  let fail_slots  () = failwith "Cannot write the *slots field"
  let fail_length () = failwith "Cannot write the *length field"

  let check_atomic_command ctbl meth c =
    match c with
    | Field_update ({node = y; ty = Tclass cname}, field, _) ->
      if cname = meth then () else (* meth is the constructor *)
      if Ctbl.is_array_like_class ctbl ~classname:cname then begin
        let fields = Ctbl.field_names ctbl ~classname:cname in
        if List.mem field.node fields then
          if field.ty = Tint then fail_length () else fail_slots ()
      end
    | _ -> ()

  let check_command ctbl meth c =
    let rec check = function
      | Acommand c -> check_atomic_command ctbl meth c
      | Vardecl (_, _, _, c) | While (_, _, c) -> check c
      | Seq (c1, c2) | If (_, c1, c2) -> check c1 ; check c2
      | _ -> () in
    check c

  let check_method_def ctbl (Method (mdecl, com)) =
    let meth_name = mdecl.meth_name.node in
    match com with
    | None   -> ()
    | Some c -> check_command ctbl meth_name c

  let check_module ctbl mdef =
    let rec loop = function
      | [] -> ()
      | Mdl_mdef m :: ms -> check_method_def ctbl m ; loop ms
      | _ :: ms -> loop ms in
    loop mdef.mdl_elts

  let check (prog, ctbl) =
    match prog with
    | Unary_interface idef -> ()
    | Unary_module mdef -> check_module ctbl mdef
    | _ -> failwith "Array_fields_wr_check.check not implemented"
end


(* -------------------------------------------------------------------------- *)
(* Driver                                                                     *)
(* -------------------------------------------------------------------------- *)

let tc_program (prog: program)
  : (T.program_elt M.t * Ctbl.t, string) result =
  (* Create an initial penv in which all modules and interfaces are Untyped. *)
  let ini_penv =
    List.fold_left (fun map prog_elt ->
        let elt = prog_elt.elt in
        M.add (get_program_elt_name elt) (Untyped elt) map
      ) M.empty prog in
  let rec loop penv env known p =
    match p with
    | [] -> ok (penv, env)
    | Unr_intr idef :: ps ->
      if !tc_debug then begin
        let name = string_of_ident idef.elt.intr_name in
        Printf.fprintf stderr "Typing: %s\n" name;
        Ctbl.debug_print_ctbl stderr env.ctbl;
      end;
      let* known = check_unique_names_interface known idef in
      let* penv, env', idef = tc_interface penv env idef in
      let _ = Array_fields_wr_check.check (Unary_interface idef, env'.ctbl) in
      loop penv env' known ps
    | Unr_mdl mdl :: ps ->
      if !tc_debug then begin
        let name = string_of_ident mdl.elt.mdl_name in
        Printf.fprintf stderr "Typing: %s\n" name;
        Ctbl.debug_print_ctbl stderr env.ctbl;
      end;
      let* known = check_unique_names_module known mdl in
      let* penv, env', mdl = tc_module penv env mdl in
      let _ = Array_fields_wr_check.check (Unary_module mdl, env'.ctbl) in
      loop penv env' known ps
    | Rel_mdl bimdl :: ps ->
      if !tc_debug then begin
        let name = string_of_ident bimdl.elt.bimdl_name in
        Printf.fprintf stderr "Typing: %s\n" name
      end;
      let* penv, env', bimdl = tc_bimodule penv initial_bi_tenv bimdl in
      loop penv env known ps in
  let prog = T.Deps.sort_by_dependencies prog in
  let prog = get_elts prog in
  let* (penv, env) = loop ini_penv initial_tenv empty_known_map prog in
  (* All known interfaces and modules must be type checked *)
  assert (M.for_all (fun _ -> function Typed _ -> true | _ -> false) penv);
  if !tc_debug then begin
    Printf.fprintf stderr "Known classes:\n";
    Ctbl.debug_print_ctbl stderr env.ctbl
  end;
  ok (to_program_map penv, env.ctbl)
