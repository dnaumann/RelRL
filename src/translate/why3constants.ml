(** constants.ml -- constants and functions expected to be in the initial Why3
    environment, plus utilities *)

open Why3
open Why3util
open Build_operators

(* -------------------------------------------------------------------------- *)
(* Basic types                                                                *)
(* -------------------------------------------------------------------------- *)

let int_type = Ptree.PTtyapp (mk_qualid ["int"], [])
let bool_type = Ptree.PTtyapp (mk_qualid ["bool"], [])
let unit_type = Ptree.PTtyapp (mk_qualid ["unit"], [])
let reference_type = Ptree.PTtyapp (mk_qualid ["reference"], [])
let rgn_type = Ptree.PTtyapp (mk_qualid ["rgn"], [])
let list_type pty = Ptree.PTtyapp (mk_qualid ["L"; "list"], [pty])


(* -------------------------------------------------------------------------- *)
(* Why3's old operator                                                        *)
(* -------------------------------------------------------------------------- *)

let old_fn = mk_qualid ["old"]
let mk_old_term t = mk_term (Tapply (mk_var (mk_ident "old"), t))


(* -------------------------------------------------------------------------- *)
(* Arithmetic                                                                 *)
(* -------------------------------------------------------------------------- *)

let div_fn = mk_qualid ["div"]
let mod_fn = mk_qualid ["mod"]


(* -------------------------------------------------------------------------- *)
(* Functions on Why3 references                                               *)
(* -------------------------------------------------------------------------- *)

let get_ref_fn = mk_qualid [Ident.op_tight "!"]
let set_ref_fn = mk_qualid [Ident.op_infix ":="]
let mk_ref_fn = mk_qualid ["ref"]

let get_ref id = mk_eapp get_ref_fn [mk_qevar id]
let get_ref_term id = mk_tapp get_ref_fn [mk_qvar id]
let set_ref id expr = mk_eapp set_ref_fn [mk_qevar id; expr]


(* -------------------------------------------------------------------------- *)
(* Equality on primitive types                                                *)
(* -------------------------------------------------------------------------- *)

(* NOTE: WhyRel modules are compiled in a Why3 context that includes [use Int].
   The [Int] module exports the [(=)] symbol for equality between integers;
   hence, a Why3 expression such as [e1 = e2] corresponds to [Int.(=) e1 e2].

   This means when comparing values of other types in expressions, we must
   resort to the functions defined below.  We don't face this issue with Why3
   terms: the term [e1 = e2] does not correspond to [Int.(=) e1 e2], but to the
   more general notion of equality. *)

let eq_rgn_fn = mk_qualid ["eqRgn"]
let eq_bool_fn = mk_qualid ["eqBool"]
let eq_unit_fn = mk_qualid ["eqUnit"]


(* -------------------------------------------------------------------------- *)
(* Constants of type reference                                                *)
(* -------------------------------------------------------------------------- *)

let null_const = mk_evar (mk_ident "null")
let null_const_term = mk_var (mk_ident "null")


(* -------------------------------------------------------------------------- *)
(* Region typed constants and functions on region expressions                 *)
(* -------------------------------------------------------------------------- *)

let empty_rgn = mk_qualid ["emptyRgn"]

let mem_fn = mk_qualid ["Rgn"; "mem"]
let diff_fn = mk_qualid ["Rgn"; "diff"]
let union_fn = mk_qualid ["Rgn"; "union"]
let inter_fn = mk_qualid ["Rgn"; "inter"]
let subset_fn = mk_qualid ["Rgn"; "subset"]
let disjoint_fn = mk_qualid [Ident.op_infix "\\#"]
let singleton_fn = mk_qualid ["singleton"]
let rgnsubK_fn = mk_qualid ["rgnSubK"]


(* -------------------------------------------------------------------------- *)
(* Functions on Finite Maps                                                   *)
(* -------------------------------------------------------------------------- *)

(* let map_mem_fn = mk_qualid [Ident.op_infix "\\:"] *)
let map_mem_fn = mk_qualid ["M"; "mem"]
let map_find_fn = mk_qualid [Ident.op_get ""]
let map_add_fn = mk_qualid ["M"; "add"]
let map_create_fn = mk_qualid ["M"; "create"]

let map_add map k v = map_add_fn <$> [k; v; map]
let map_empty_expr = map_create_fn <$> [mk_expr (Etuple [])]
let map_mem map k = map_mem_fn <$> [k; map]
let map_find map k =
  let find_fn = mk_qualid [Ident.op_get ""] in
  find_fn <$> [map; k]


(* -------------------------------------------------------------------------- *)
(* Functions on mathematical arrays (defined in stdlib/Whyrel_array)          *)
(* -------------------------------------------------------------------------- *)

let array_get_fn = mk_qualid ["A"; "get"]
let array_set_fn = mk_qualid ["A"; "set"]
let array_make_fn = mk_qualid ["A"; "make"]
let array_len_fn = mk_qualid ["A"; "length"]


(* -------------------------------------------------------------------------- *)
(* Why3 list constants and functions                                          *)
(* -------------------------------------------------------------------------- *)

let list_mem_fn = mk_qualid ["L"; "mem"]
let list_cons_fn = mk_qualid ["L"; "Cons"]
let list_nil = mk_qualid ["L"; "Nil"]


(* -------------------------------------------------------------------------- *)
(* WhyRel's ``Type'' predicate                                                *)
(* -------------------------------------------------------------------------- *)

let typeof_rgn_fn = mk_qualid ["typeofRgn"]


(* -------------------------------------------------------------------------- *)
(* Functions on prerefperms                                                   *)
(* -------------------------------------------------------------------------- *)

let id_ref_fn = mk_qualid ["PreRefperm"; "idRef"]
let id_rgn_fn = mk_qualid ["PreRefperm"; "idRgn"]
let update_refperm = mk_qualid ["PreRefperm"; "updateRefperm"]
let invert_refperm = mk_qualid ["PreRefperm"; "invert"]
let identity_refperm = mk_qualid ["PreRefperm"; "identity"]
let extends_refperm = mk_qualid ["PreRefperm"; "extends"]


(* -------------------------------------------------------------------------- *)
(* Standard import declarations                                               *)
(* -------------------------------------------------------------------------- *)

let import_prelude = use_import ["prelude"; "Prelude"]
let import_refperm = use_import ["prelude"; "PreRefperm"]


(* -------------------------------------------------------------------------- *)
(* Special Why3 labels                                                        *)
(* -------------------------------------------------------------------------- *)

let init_label = mk_ident "INIT"
