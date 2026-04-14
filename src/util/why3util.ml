(** why3util -- utility functions to work with Why3 *)

open Lib
open Why3


(* -------------------------------------------------------------------------- *)
(* Utility structures                                                         *)
(* -------------------------------------------------------------------------- *)

module Ordered_Ptree_qualid =
struct
  type t = Ptree.qualid

  let rec compare s t =
    let open Ptree in
    let comp = Stdlib.compare in
    match s, t with
    | Qident s, Qident t -> comp s.id_str t.id_str
    | Qident s, _ -> -1
    | _, Qident s -> 1
    | Qdot (qs, s), Qdot (qt, t) ->
      let res = compare qs qt in
      if res = 0 then comp s.id_str t.id_str else res
end

module QualidS = Set.Make (Ordered_Ptree_qualid)
module QualidM = Map.Make (Ordered_Ptree_qualid)


(* -------------------------------------------------------------------------- *)
(* Constructing parse trees                                                   *)
(* -------------------------------------------------------------------------- *)

(* Taken from Why3's API tutorials *)

let mk_ident (s: string) : Ptree.ident =
  { id_str = s;
    id_ats = [];
    id_loc = Mlw_printer.next_pos () }

let mk_qualid (l: string list) : Ptree.qualid =
  let rec aux l =
    match l with
    | [] -> assert false
    | [x] -> Ptree.Qident(mk_ident x)
    | x::r -> Ptree.Qdot(aux r, mk_ident x) in
  aux (List.rev l)

let string_list_of_qualid (q: Ptree.qualid) : string list =
  let rec aux l = function
    | Ptree.Qident x -> x.id_str :: l
    | Ptree.Qdot (ql, x) -> aux (x.id_str :: l) ql in
  aux [] q

let string_of_qualid (q: Ptree.qualid) : string =
  String.concat "." (string_list_of_qualid q)

let qualid_of_ident (id: Ptree.ident) : Ptree.qualid =
  mk_qualid [id.id_str]

let ident_of_qualid (ql: Ptree.qualid) : Ptree.ident =
  match ql with
  | Qident id -> id
  | Qdot _ -> invalid_arg "ident_of_qualid"

let mk_infix (op: string) : Ptree.ident =
  mk_ident (Ident.op_infix op)

let use_import (l: string list) : Ptree.decl =
  let qid_id_opt = (mk_qualid l, None) in
  Duseimport (Mlw_printer.next_pos (), false, [qid_id_opt])

let use_export (l: string list) : Ptree.decl =
  let qid = mk_qualid l in
  Duseexport qid

let mk_expr (e: Ptree.expr_desc) : Ptree.expr =
  { expr_desc = e;
    expr_loc = Mlw_printer.next_pos () }

let mk_term (t: Ptree.term_desc) : Ptree.term =
  { term_desc = t;
    term_loc = Mlw_printer.next_pos () }

let mk_pat (p: Ptree.pat_desc) : Ptree.pattern =
  { pat_desc = p;
    pat_loc = Mlw_printer.next_pos () }

let pat_var (id: Ptree.ident) : Ptree.pattern =
  mk_pat (Pvar id)

let pat_wild : Ptree.pattern =
  mk_pat Pwild

let mk_var (id: Ptree.ident) : Ptree.term =
  mk_term (Tident (Qident id))

let mk_qvar (id: Ptree.qualid) : Ptree.term =
  mk_term (Tident id)

let param0 = [Mlw_printer.next_pos (), None, false, Some (Ptree.PTtuple [])]
let param1 id ty = [Mlw_printer.next_pos (), Some id, false, Some ty]

let mk_const (i: int) : Constant.constant =
  Constant.(ConstInt Number.{ il_kind = ILitDec; il_int = BigInt.of_int i})

let mk_tconst (i: int) : Ptree.term = mk_term (Tconst (mk_const i))

let mk_econst (i: int) : Ptree.expr = mk_expr (Econst (mk_const i))

let mk_tapp (f: Ptree.qualid) (l: Ptree.term list) : Ptree.term =
  mk_term (Tidapp (f, l))

let mk_tapply (f: Ptree.term) (l: Ptree.term list) : Ptree.term =
  (* curried application of a term to a term *)
  foldl1 (fun f x -> mk_term (Tapply(f,x))) (f :: l)

let mk_eapp (f: Ptree.qualid) (l: Ptree.expr list) : Ptree.expr =
  mk_expr (Ptree.Eidapp (f, l))

let mk_evar (x: Ptree.ident) : Ptree.expr = mk_expr (Eident (Qident x))

let mk_qevar (x: Ptree.qualid) : Ptree.expr = mk_expr (Eident x)

let mk_param id gho ty : Ptree.param =
  (Mlw_printer.next_pos (), Some id, gho, ty)

let mk_binder x gho (ty: Ptree.pty option) : Ptree.binder =
  (Mlw_printer.next_pos (), Some x, gho, ty)

let mk_quant quantif binders frm : Ptree.term =
  mk_term @@ Tquant (quantif, binders, [], frm)

(* mk_implies [t1; t2; ...; tn] = ``t1 -> t2 -> ... -> tn'' *)
let mk_implies (ts: Ptree.term list) : Ptree.term =
  if is_nil ts then failwith "mk_implies: empty list"
  else foldr1 (fun h t -> mk_term (Tbinop (h, Dterm.DTimplies, t))) ts

(* mk_conjs [t1; t2; ...; tn] = ``t1 /\ t2 /\ ... /\ tn'' *)
let mk_conjs (ts: Ptree.term list) : Ptree.term =
  if is_nil ts then failwith "mk_conjs: empty list"
  else foldr1 (fun h t -> mk_term (Tbinop (h, Dterm.DTand, t))) ts

(* safe_mk_conjs ts = ts'

   if ts = [], then ts' = []
   otherwise ts' = mk_conjs ts
 *)
let safe_mk_conjs (ts: Ptree.term list) : Ptree.term list =
  match ts with
  | [] -> []
  | _ -> [mk_conjs ts]

let mk_conjs_default (ts: Ptree.term list) (t: Ptree.term) : Ptree.term =
  let conj t1 t2 = mk_term (Tbinop (t1, Dterm.DTand, t2)) in
  foldr1 conj (t::ts)

let mk_spec pre post reads writes : Ptree.spec =
  { sp_pre = pre;               (* preconditions *)
    sp_post = post;             (* postconditions *)
    sp_xpost = [];              (* exceptional postconditions *)
    sp_reads = reads;           (* reads clause *)
    sp_writes = writes;         (* writes clause *)
    sp_alias = [];              (* alias clause *)
    sp_variant = [];            (* variant for recursive functions *)
    sp_checkrw = false;         (* should reads and writes be checked? *)
    sp_diverge = false;         (* does the function diverge? *)
    sp_partial = false          (* is the function partial? *)
  }

let empty_spec : Ptree.spec = mk_spec [] [] [] []

let mk_spec_simple pre post writes : Ptree.spec =
  { sp_pre = pre;
    sp_post = post;
    sp_xpost = [];
    sp_reads = [];
    sp_writes = writes;
    sp_alias = [];
    sp_variant = [];
    sp_checkrw = false;
    sp_diverge = false;
    sp_partial = false
  }

let mk_ldecl ident params lty def : Ptree.logic_decl =
  { ld_loc = Mlw_printer.next_pos ();
    ld_ident = ident;
    ld_params = params;
    ld_type = Some lty;
    ld_def = def
  }

let mk_abstract_expr params ret_ty spec : Ptree.expr =
  let mask = Ity.MaskVisible in
  mk_expr @@ Eany (params, Expr.RKnone, Some ret_ty, mk_pat Pwild, mask, spec)

let mk_ensures frm : Ptree.post =
  Mlw_printer.next_pos (), [pat_var (mk_ident "result"), frm]


(* -------------------------------------------------------------------------- *)
(* Default definitions                                                        *)
(* -------------------------------------------------------------------------- *)

let mk_pair_ty t1 t2 : Ptree.pty = PTtuple [t1; t2]

let rec mk_explain_attr msg =
  let expl = "expl:" ^ msg in
  Ptree.ATstr (Ident.create_attribute expl)

and explain_term t msg = mk_term (Tattr (mk_explain_attr msg, t))
and explain_expr t msg = mk_expr (Eattr (mk_explain_attr msg, t))

let suppress_unused_warning term =
  let unused = Ident.create_attribute "W:unused_variable:N" in
  mk_term (Tattr (Ptree.ATstr unused, term))


(* -------------------------------------------------------------------------- *)
(* Wrappers around Why3 pretty printing functions                             *)
(* -------------------------------------------------------------------------- *)

let wrap_pp pp e : unit =
  pp Format.std_formatter e;
  Format.pp_print_newline Format.std_formatter ();
  Format.pp_print_flush Format.std_formatter ()

let show_pty  = wrap_pp (Mlw_printer.pp_pty ~attr:true).closed
let show_expr = wrap_pp (Mlw_printer.pp_expr ~attr:true).closed
let show_term = wrap_pp (Mlw_printer.pp_term ~attr:true).closed
let show_decl = wrap_pp Mlw_printer.pp_decl
let show_mlw  = wrap_pp Mlw_printer.pp_mlw_file

(* -------------------------------------------------------------------------- *)
(* Convenient forms for building Why3 parse trees                             *)
(* -------------------------------------------------------------------------- *)

module Build_operators = struct
  (* DO NOT rely on operator precedences and associativity when using
     this module.  Parenthesize! *)

  (* right associative *)
  let ( ^==> ) t1 t2 = mk_term (Tbinnop (t1, Dterm.DTimplies, t2))

  (* left associative *)
  let ( <==> ) t1 t2 = mk_term (Tbinnop (t1, Dterm.DTiff, t2))

  (* left associative *)
  let ( ==. ) t1 t2 = mk_term (Tinnfix (t1, mk_infix "=", t2))

  let ( =/=. ) t1 t2 = mk_term (Tinnfix (t1, mk_infix "<>", t2))

  (* right associative *)
  let ( ^&& ) t1 t2 = mk_term (Tbinnop (t1, Dterm.DTand, t2))

  let ( ^& ) e1 e2 = mk_expr (Eand (e1, e2))

  (* right associative *)
  let ( ^|| ) t1 t2 = mk_term (Tbinnop (t1, Dterm.DTor, t2))

  let ( ^| ) e1 e2 = mk_expr (Eor (e1, e2))

  (* prefix *)
  let ( ~. ) x = mk_ident x

  (* prefix *)
  let ( ~* ) x = mk_var x

  (* prefix *)
  let ( ~% ) x = mk_term x

  (* prefix *)
  let ( ~^ ) x = mk_expr (Enot x)

  (* left associative *)
  let ( %. ) s f = Ptree.Qdot(s, f)

  let mk_term_app f args =
    List.fold_left (fun acc e -> mk_term (Tapply (acc, e))) (mk_qvar f) args

  (* left associative *)
  let ( <*> ) f args = mk_term (Tidapp(f, args))
  let ( <$> ) f args = mk_expr (Eidapp(f, args))

  let bindvar (x, ty) s = ((x, ty), s)
  let return t s = (t, s)
  let build_term (t: 's -> ('a * 's)) = fst (t [])

  (* let+! and let+? can be used to create universally and
     existentially quantified formulas.  For example, one may say

         let+! p = bindvar (mk_ident "p", int_type) in
         let+? q = bindvar (mk_ident "q", int_type) in
         return ((mk_var p) ==. (mk_var q))

     to build the Why3 term: (forall p:int. exists q:int. p = q).

     Sequences of forall's and exist's are handled so that

         let+! p = bindvar (mk_ident "p", ...) in
         let+! q = bindvar (mk_ident "q", ...) in
         ...

     generates (forall p:int, q:int. ...) instead of
     (forall p:int. forall q:int. ...).
     Such chains are appropriately broken if quantifiers are mixed.
  *)
  let ( let+! ) (m: 's->('a*'s)) (k: 'a->'s->('b*'s)) : 's->('b*'s) = fun s ->
    let (x, ty), binders = m s in
    let term, binders' = k (x, ty) binders in
    let xbind = mk_binder x false (Some ty) in
    match term.Ptree.term_desc with
    | Tquant(Dterm.DTforall, _, metas, inner) ->
      let binds = xbind :: binders' in
      let term' = mk_term (Tquant(Dterm.DTforall, binds, metas, inner)) in
      term', binds
    | Tquant(Dterm.DTexists, _, _, _) ->
      let term' = mk_term (Tquant(Dterm.DTforall, [xbind], [], term)) in
      term', [xbind]
    | _ ->
      let binds = xbind :: binders' in
      let term' = mk_term (Tquant(Dterm.DTforall, binds, [], term)) in
      term', binds

  let ( let+? ) (m: 's->('a*'s)) (k: 'a->'s->('b*'s)) : 's->('b*'s) = fun s ->
    let (x, ty), binders = m s in
    let (term, binders') = k (x, ty) binders in
    let xbind = mk_binder x false (Some ty) in
    match term.Ptree.term_desc with
    | Tquant (Dterm.DTexists, _, metas, inner) ->
      let binds = xbind :: binders' in
      let term' = mk_term (Tquant(Dterm.DTexists, binds, metas, inner)) in
      term', binds
    | Tquant (Dterm.DTforall, _, _, _) ->
      let term' = mk_term (Tquant(Dterm.DTexists, [xbind], [], term)) in
      term', [xbind]
    | _ ->
      let binds = xbind :: binders' in
      let term' = mk_term (Tquant(Dterm.DTexists, binds, [], term)) in
      term', binds
end


(* -------------------------------------------------------------------------- *)
(* Functions on Why3 expressions and terms                                    *)
(* -------------------------------------------------------------------------- *)

let rec reassoc_expr (e: Ptree.expr) : Ptree.expr =
  match e.expr_desc with
  | Esequence (e1, e2) ->
    let e1' = reassoc_expr e1 in
    let e2' = reassoc_expr e2 in
    begin match e1'.expr_desc with
      | Esequence (d1, d2) ->
        let inner = reassoc_expr @@ mk_expr (Esequence (d2, e2')) in
        mk_expr (Esequence (d1, inner))
      | _ -> mk_expr (Esequence (e1', e2'))
    end
  | Elet (x, gho, k, v, e) -> mk_expr (Elet (x, gho, k, v, reassoc_expr e))
  | Eif (b, e1, e2) -> mk_expr (Eif (b, reassoc_expr e1, reassoc_expr e2))
  | Ewhile (e, inv, v, body) -> mk_expr (Ewhile (e, inv, v, reassoc_expr body))
  | Elabel (l, e) -> mk_expr (Elabel (l, reassoc_expr e))
  | Escope (q, e) -> mk_expr (Escope (q, reassoc_expr e))
  | Eattr (attr, e) -> mk_expr (Eattr (attr, reassoc_expr e))
  | Efun (bs, ty, pat, mask, spec, e) ->
    mk_expr (Efun (bs, ty, pat, mask, spec, reassoc_expr e))
  | Erec (fdefs, e) -> mk_expr (Erec (fdefs, reassoc_expr e))
  | _ -> e

(* Rewrite (); e and e; () to e *)
let rec simplify_expr (e: Ptree.expr) : Ptree.expr =
  match e.expr_desc with
  | Esequence (e1, e2) ->
    let e1' = simplify_expr e1 in
    let e2' = simplify_expr e2 in
    begin match e1'.expr_desc, e2'.expr_desc with
      | Etuple [], d | d, Etuple [] -> mk_expr d
      | _, _ -> mk_expr (Esequence (e1', e2'))
    end
  | Elet (x, gho, k, v, e) -> mk_expr (Elet (x, gho, k, v, simplify_expr e))
  | Eif (b, e1, e2) -> mk_expr (Eif (b, simplify_expr e1, simplify_expr e2))
  | Ewhile (e, inv, v, body) -> mk_expr (Ewhile (e, inv, v, simplify_expr body))
  | Elabel (l, e) -> mk_expr (Elabel (l, simplify_expr e))
  | Escope (q, e) -> mk_expr (Escope (q, simplify_expr e))
  | Eattr (attr, e) -> mk_expr (Eattr (attr, simplify_expr e))
  | Efun (bs, ty, pat, mask, spec, e) ->
    mk_expr (Efun (bs, ty, pat, mask, spec, simplify_expr e))
  | Erec (fdefs, e) -> mk_expr (Erec (fdefs, simplify_expr e))
  | _ -> e

let rec simplify_term (t: Ptree.term) : Ptree.term =
  match t.term_desc with
  | Tbinop (t1, op, t2) ->
    let t1' = simplify_term t1 in
    let t2' = simplify_term t2 in
    begin match op, t1'.term_desc, t2'.term_desc with
      | Dterm.DTand, Ttrue, t  | Dterm.DTand, t, Ttrue -> mk_term t
      | Dterm.DTand, Tfalse, t | Dterm.DTand, t, Tfalse -> mk_term Tfalse
      | Dterm.DTor, Ttrue, t   | Dterm.DTor, t, Ttrue -> mk_term Ttrue
      | Dterm.DTor, Tfalse, t  | Dterm.DTor, t, Tfalse -> mk_term t
      | _, _, _ -> mk_term (Tbinop (t1', op, t2'))
    end    
  | Tbinnop (t1, op, t2) ->
    let t1' = simplify_term t1 in
    let t2' = simplify_term t2 in
    begin match op, t1'.term_desc, t2'.term_desc with
      | Dterm.DTand, Ttrue, t  | Dterm.DTand, t, Ttrue -> mk_term t
      | Dterm.DTand, Tfalse, t | Dterm.DTand, t, Tfalse -> mk_term Tfalse
      | Dterm.DTor, Ttrue, t   | Dterm.DTor, t, Ttrue -> mk_term Ttrue
      | Dterm.DTor, Tfalse, t  | Dterm.DTor, t, Tfalse -> mk_term t
      | _, _, _ -> mk_term (Tbinnop (t1', op, t2'))
    end
  | Tnot t ->
    let t' = simplify_term t in
    begin match t'.term_desc with
      | Ttrue -> mk_term Tfalse
      | Tfalse -> mk_term Ttrue
      | _ -> mk_term (Tnot t')
    end
  | Tidapp (q, ts) -> mk_term (Tidapp (q, map simplify_term ts))
  | Tquant (q, bs, rng, t) -> mk_term (Tquant (q, bs, rng, simplify_term t))
  | Tattr (attr, t) -> mk_term (Tattr (attr, simplify_term t))
  | Tcast (t, pty) -> mk_term (Tcast (simplify_term t, pty))
  | Ttuple ts -> mk_term (Ttuple (map simplify_term ts))
  | Tif (b, t1, t2) ->
    mk_term (Tif (simplify_term b, simplify_term t1, simplify_term t2))
  | Teps (x, pty, t) -> mk_term (Teps (x, pty, simplify_term t))
  | Tat (t, label) -> mk_term (Tat (simplify_term t, label))
  | Tlet (x, v, t) -> mk_term (Tlet (x, simplify_term v, simplify_term t))
  | Trecord qs -> mk_term (Trecord (map (fun (q,t) -> (q,simplify_term t)) qs))
  | _ -> t

let subst_term (s: (Ptree.qualid * Ptree.term) list) (t: Ptree.term) =
  let open Ptree in
  let tag = ref 0 in
  let refresh (s: string) : string = incr tag; s ^ Int.to_string !tag in
  let refresh_ident (s: ident) : ident = mk_ident (refresh s.id_str) in
  let warn_unsupported tm =
    Format.fprintf Format.err_formatter
      "subst_term: unsupported term: WhyRel not expected to generate %a\n"
      (Mlw_printer.pp_term ~attr:true).closed tm in
  let rec aux s trm = match trm.term_desc with
    | Ttrue | Tfalse | Tconst _ -> trm
    | Tident x -> (try assoc x s with Not_found -> trm)
    | Tasref x -> warn_unsupported trm; (try assoc x s with Not_found -> trm)
    | Tidapp (f, ts) ->
      begin match assoc f s with
        | {term_desc = Tident f'} -> mk_term (Tidapp (f', map (aux s) ts))
        | f' -> mk_tapply f' (map (aux s) ts)
        | exception Not_found -> mk_term (Tidapp (f, map (aux s) ts))
      end
    | Tapply (f, x) -> mk_term (Tapply (aux s f, aux s x))
    | Tinfix (t1, op, t2) -> mk_term (Tinfix (aux s t1, op, aux s t2))
    | Tbinop (t1, op, t2) -> mk_term (Tbinop (aux s t1, op, aux s t2))
    | Tinnfix (t1, op, t2) -> mk_term (Tinnfix (aux s t1, op, aux s t2))
    | Tbinnop (t1, op, t2) -> mk_term (Tbinnop (aux s t1, op, aux s t2))
    | Tnot t -> mk_term (Tnot (aux s t))
    | Tif (e, t1, t2) -> mk_term (Tif (aux s e, aux s t1, aux s t2))
    | Tquant (q, bnds, trigs, tm) ->
      (* You only have to rename a bound variable x if s contains the mapping
         y |-> e with x in FV(e).  But it's simpler to always rename, so this
         is what we'll do. *)
      let refresh_opt = Option.map refresh_ident in
      let mk_id e = Tident (qualid_of_ident e) in
      let names = map (fun (_,id,_,_) -> id) bnds in

      let refresh_binder (loc, name, gho, ty) =
        let name' = Option.map refresh_ident name in
        (loc, name', gho, ty) in

      let bnds' = map (Option.map mk_id % refresh_opt) names in
      let bndtms = map (Option.map mk_term) bnds' in
      (* new substitutions *)
      let s' = filter (Option.is_some % fst) (List.combine names bndtms) in
      let s' = map (cross Option.(get, get)) s' in
      (* subst s (forall x. p) =
           let x' = refresh x in
           (forall x'. subst ((x,x') :: s) p) *)
      
      failwith "HERE"
    | _ -> failwith "not implemented" in
  aux s t

let elim_let (trm: Ptree.term) : Ptree.term =
  let open Ptree in
  let tag = ref 0 in
  let refresh_name (s: string) : string = s ^ Int.to_string !tag in

  let warn_unsupported tm =
    Format.fprintf Format.err_formatter
      "elim_let: unsupported term: WhyRel not expected to generate %a\n"
      (Mlw_printer.pp_term ~attr:true).closed tm in

  let ret term_desc = {term_desc; term_loc = Mlw_printer.next_pos ()} in

  let rec aux subs trm = match trm.term_desc with
    | Ttrue -> trm
    | Tfalse -> trm
    | Tconst c -> trm
    | Tident x ->
      begin try assoc x subs with Not_found -> trm end
    | Tasref x ->
      warn_unsupported trm;
      begin try assoc x subs with Not_found -> trm end
    | Tidapp (q, ts) -> ret (Tidapp (q, map (aux subs) ts))
    | Tapply (t1, t2) -> ret (Tapply (aux subs t1, aux subs t2))
    | Tinfix (t1, f, t2) -> ret (Tinfix (aux subs t1, f, aux subs t2))
    | Tinnfix (t1, f, t2) -> ret (Tinnfix (aux subs t1, f, aux subs t2))
    | Tbinop (t1, op, t2) -> ret (Tbinop (aux subs t1, op, aux subs t2))
    | Tbinnop (t1, op, t2) -> ret (Tbinnop (aux subs t1, op, aux subs t2))
    | Tnot t -> ret (Tnot (aux subs t))
    | Tif (e, t1, t2) -> ret (Tif (aux subs e, aux subs t1, aux subs t2))
    | Teps (id, ty, t) -> warn_unsupported trm; ret (Teps (id, ty, aux subs t))
    | Tattr (attr, t) -> ret (Tattr (attr, aux subs t))
    | Tlet (id, e, tm) ->
      failwith "WORKING HERE"
    | Tquant (q, bs, triggers, tm) -> failwith "WORKING HERE"
    | Tcase (tm, pats) -> failwith "WORKING HERE"
    | Trecord rs -> failwith "WORKING HERE"
    | Tupdate (t, upds) -> failwith "WORKING HERE"
    | Tscope (q, tm) -> failwith "WORKING HERE"
    | Tat (tm, i) -> failwith "WORKING HERE"
    | Ttuple ts -> ret (Ttuple (map (aux subs) ts))
    | Tcast (tm, ty) -> failwith "WORKING HERE" in

  aux [] trm

