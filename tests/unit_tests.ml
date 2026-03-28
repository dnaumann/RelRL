(** unit_tests.ml -- OUnit2 tests for lib.ml, gensym.ml, and astutil.ml *)

open OUnit2

(* Pull in the modules under test (compiled alongside this file) *)
(* Lib, Gensym, Ast, Astutil are available via the include paths *)


(* ===================================================================== *)
(* Tests for Lib                                                          *)
(* ===================================================================== *)

let test_lib_basic _ =
  (* id *)
  assert_equal 42 (Lib.id 42);
  assert_equal "hello" (Lib.id "hello");
  (* const *)
  assert_equal 5 (Lib.const 5 ());
  assert_equal "x" (Lib.const "x" 99);
  (* flip *)
  assert_equal 7 (Lib.flip (-) 3 10);
  assert_equal [1;2] (Lib.flip List.cons [2] 1);
  (* dup *)
  assert_equal 6 (Lib.dup ( + ) 3);
  (* cross *)
  assert_equal (4, 4) (Lib.cross (succ, pred) (3, 5));
  (* fork *)
  assert_equal (6, 4) (Lib.fork (succ, pred) 5);
  (* on *)
  assert_equal 0 (Lib.on compare String.length "ab" "cd");
  (* uncurry / curry *)
  assert_equal 7 (Lib.uncurry ( + ) (3, 4));
  assert_equal 1 (Lib.curry fst 1 2);
  (* pair / triple *)
  assert_equal (1, 2) (Lib.pair 1 2);
  assert_equal (1, 2, 3) (Lib.triple 1 2 3);
  (* map_pair *)
  assert_equal (4, 5) (Lib.map_pair succ (3, 4));
  (* dup_pair *)
  assert_equal (5, 5) (Lib.dup_pair 5)

let test_lib_total_partial _ =
  let safe_div a b = if b = 0 then failwith "div by zero" else a / b in
  assert_equal (Some 5) (Lib.total (safe_div 10) 2);
  assert_equal None     (Lib.total (safe_div 10) 0);
  assert_equal true  (Lib.can (safe_div 10) 2);
  assert_equal false (Lib.can (safe_div 10) 0)

let test_lib_check _ =
  assert_equal 5 (Lib.check (fun x -> x > 0) 5);
  assert_raises (Failure "check") (fun () -> Lib.check (fun x -> x > 0) (-1));
  assert_equal (Some 5) (Lib.check_opt (fun x -> x > 0) 5);
  assert_equal None     (Lib.check_opt (fun x -> x > 0) (-1))

let test_lib_lists_basic _ =
  assert_equal 3 (Lib.last [1; 2; 3]);
  assert_raises (Failure "last") (fun () -> Lib.last []);
  assert_equal true  (Lib.is_nil []);
  assert_equal false (Lib.is_nil [1]);
  assert_equal true  (Lib.elem_of [1; 2; 3] 2);
  assert_equal false (Lib.elem_of [1; 2; 3] 4)

let test_lib_split_at _ =
  assert_equal ([1;2], [3;4;5]) (Lib.split_at 2 [1;2;3;4;5]);
  assert_equal ([], [1;2;3])    (Lib.split_at 0 [1;2;3]);
  assert_equal ([1;2;3], [])    (Lib.split_at 3 [1;2;3]);
  assert_equal ([], [])         (Lib.split_at 0 [])

let test_lib_take_drop _ =
  assert_equal [1;2;3] (Lib.take 3 [1;2;3;4;5]);
  assert_equal [1;2;3] (Lib.take 5 [1;2;3]);
  assert_equal []      (Lib.take 0 [1;2;3]);
  assert_equal [3;4;5] (Lib.drop 2 [1;2;3;4;5]);
  assert_equal []      (Lib.drop 5 [1;2;3]);
  assert_equal [1;2;3] (Lib.drop 0 [1;2;3])

let test_lib_take_while_drop_while _ =
  assert_equal [1;2;3] (Lib.take_while (fun x -> x < 4) [1;2;3;4;5]);
  assert_equal []      (Lib.take_while (fun x -> x > 10) [1;2;3]);
  assert_equal [4;5]   (Lib.drop_while (fun x -> x < 4) [1;2;3;4;5]);
  assert_equal []      (Lib.drop_while (fun _ -> true) [1;2;3])

let test_lib_no_duplicates _ =
  assert_equal true  (Lib.no_duplicates [1;2;3]);
  assert_equal true  (Lib.no_duplicates []);
  assert_equal false (Lib.no_duplicates [1;2;1]);
  assert_equal false (Lib.no_duplicates [1;1]);
  assert_equal true  (Lib.is_unique ['a'; 'b'; 'c'])

let test_lib_nub _ =
  assert_equal [1;2;3]   (Lib.nub [1;2;1;3;2]);
  assert_equal [1;2;3]   (Lib.nub [1;2;3]);
  assert_equal []         (Lib.nub []);
  assert_equal ['a']      (Lib.nub ['a';'a';'a'])

let test_lib_destutter _ =
  assert_equal [1;2;3;4] (Lib.destutter [1;1;2;3;3;3;4]);
  assert_equal [1;2;3]   (Lib.destutter [1;2;3]);
  assert_equal []         (Lib.destutter []);
  assert_equal [1]        (Lib.destutter [1;1;1])

let test_lib_unzip _ =
  assert_equal ([1;2], ['a';'b']) (Lib.unzip [(1,'a');(2,'b')]);
  assert_equal ([], []) (Lib.unzip [])

let test_lib_interleave _ =
  assert_equal [1;2;3;4] (Lib.interleave [1;3] [2;4]);
  assert_equal []         (Lib.interleave [] []);
  assert_equal [1;2]      (Lib.interleave [1] [2])

let test_lib_tabulate_replicate _ =
  assert_equal [0;2;4;6] (Lib.tabulate (fun i -> i*2) 4);
  assert_equal []        (Lib.tabulate (fun i -> i) 0);
  assert_equal ['x';'x';'x'] (Lib.replicate 3 'x');
  assert_equal []             (Lib.replicate 0 'y')

let test_lib_folds _ =
  (* foldl: like fold_left but with flipped arguments *)
  assert_equal 15 (Lib.foldl ( + ) 0 [1;2;3;4;5]);
  (* foldr: fold_right *)
  assert_equal [1;2;3] (Lib.foldr (fun h t -> h::t) [] [1;2;3]);
  (* foldr1 *)
  assert_equal 6 (Lib.foldr1 ( + ) [1;2;3]);
  assert_raises (Failure "foldr1: empty list") (fun () -> Lib.foldr1 ( + ) []);
  (* foldl1 *)
  assert_equal 6  (Lib.foldl1 ( + ) [1;2;3]);
  assert_raises (Failure "foldl1: empty list") (fun () -> Lib.foldl1 ( + ) [])

let test_lib_scan _ =
  assert_equal [0;1;3;6]  (Lib.scanl ( + ) 0 [1;2;3]);
  assert_equal [6;5;3;0]  (Lib.scanr ( + ) 0 [1;2;3])

let test_lib_concat_map _ =
  assert_equal [1;2;2;3;3;3] (Lib.concat_map (fun n -> Lib.replicate n n) [1;2;3]);
  assert_equal [] (Lib.concat_map (fun _ -> []) [1;2;3]);
  assert_equal [] (Lib.concat_map (fun n -> [n]) [])

let test_lib_set_ops _ =
  assert_equal [1;2;3;4] (List.sort compare (Lib.union [1;2;3] [2;3;4]));
  assert_equal [2;3]     (Lib.intersect [1;2;3] [2;3;4]);
  assert_equal [1]       (Lib.diff [1;2;3] [2;3;4]);
  assert_equal true  (Lib.subset [1;2] [1;2;3]);
  assert_equal false (Lib.subset [1;4] [1;2;3]);
  assert_equal true  (Lib.set_eq [1;2;3] [3;2;1]);
  assert_equal false (Lib.set_eq [1;2] [1;2;3])

let test_lib_ucons _ =
  assert_equal [1;2;3] (Lib.ucons 2 [1;2;3]);
  let r = Lib.ucons 4 [1;2;3] in
  assert_equal true (List.mem 4 r && List.length r = 4)

let test_lib_rev_assoc _ =
  assert_equal ("x", 1) (Lib.rev_assoc 1 [("x", 1); ("y", 2)]);
  assert_raises Not_found (fun () -> Lib.rev_assoc 99 [("x", 1)])

let test_lib_first _ =
  let evens x = if x mod 2 = 0 then Some x else None in
  assert_equal 4 (Lib.first evens [1;3;4;6]);
  assert_raises Not_found (fun () -> Lib.first evens [1;3;5]);
  assert_equal (Some 4) (Lib.first_opt evens [1;3;4;6]);
  assert_equal None     (Lib.first_opt evens [1;3;5])

let test_lib_strings _ =
  assert_equal "HELLO" (Lib.uppercase "hello");
  assert_equal "hello" (Lib.lowercase "HELLO");
  assert_equal "(foo)"  (Lib.parens "foo");
  assert_equal "\"bar\"" (Lib.quote "bar");
  assert_equal "[hi]"  (Lib.enclose "[" "]" "hi");
  (* explode / implode roundtrip *)
  let s = "hello" in
  assert_equal s (Lib.implode (Lib.explode s));
  assert_equal [] (Lib.explode "");
  assert_equal "" (Lib.implode [])

let test_lib_getchar _ =
  assert_equal (Some ('h', "ello")) (Lib.getchar "hello");
  assert_equal None (Lib.getchar "")

let test_lib_option_monad _ =
  let open Lib.Option in
  let open Monad_syntax in
  (* bind *)
  let r = let* x = Some 3 in let* y = Some 4 in return (x + y) in
  assert_equal (Some 7) r;
  (* short-circuit *)
  let r2 = let* _ = None in return 42 in
  assert_equal None r2;
  (* and* (parallel bind) *)
  let r3 = let* x = Some 1 and* y = Some 2 in return (x, y) in
  assert_equal (Some (1, 2)) r3;
  let r4 = let* _ = None and* _ = Some 1 in return () in
  assert_equal None r4;
  (* <|> *)
  assert_equal (Some 1) (Some 1 <|> Some 2);
  assert_equal (Some 2) (None   <|> Some 2);
  (* sequence *)
  assert_equal (Some [1;2;3]) (sequence [Some 1; Some 2; Some 3]);
  assert_equal None           (sequence [Some 1; None; Some 3]);
  (* map2 *)
  assert_equal (Some 7) (map2 ( + ) (Some 3) (Some 4));
  assert_equal None     (map2 ( + ) None (Some 4));
  (* guard *)
  assert_equal (Some ()) (guard true);
  assert_equal None      (guard false)

let test_lib_result_monad _ =
  let open Lib.Result in
  let open Monad_syntax in
  let r = let* x = Ok 3 in let* y = Ok 4 in return (x + y) in
  assert_equal (Ok 7) r;
  let r2 = let* _ = Error "oops" in return 42 in
  assert_equal (Error "oops") r2;
  (* and* *)
  let r3 = let* x = Ok 1 and* y = Ok 2 in return (x + y) in
  assert_equal (Ok 3) r3;
  let r4 = let* _ = Error "e1" and* _ = Ok 1 in return () in
  (match r4 with Error _ -> () | Ok _ -> assert_failure "expected Error");
  (* <|> *)
  assert_equal (Ok 1)        (Ok 1    <|> Ok 2);
  assert_equal (Ok 2)        (Error 0 <|> Ok 2);
  (* sequence *)
  assert_equal (Ok [1;2;3])   (sequence [Ok 1; Ok 2; Ok 3]);
  (match sequence [Ok 1; Error "e"; Ok 3] with
   | Error _ -> ()
   | Ok _    -> assert_failure "expected Error");
  (* map2 *)
  assert_equal (Ok 7) (map2 ( + ) (Ok 3) (Ok 4));
  (match map2 ( + ) (Error "e") (Ok 4) with
   | Error _ -> ()
   | Ok _    -> assert_failure "expected Error");
  (* guard *)
  assert_equal (Ok ())       (guard true  "msg");
  assert_equal (Error "msg") (guard false "msg")

let test_lib_fix _ =
  (* Test the fixpoint combinator with factorial *)
  let fact = Lib.fix (fun self n -> if n <= 0 then 1 else n * self (n-1)) in
  assert_equal 1   (fact 0);
  assert_equal 1   (fact 1);
  assert_equal 120 (fact 5)

let test_lib_add_to_list _ =
  let l = ref [1;2;3] in
  Lib.add_to_list l 0;
  assert_equal [0;1;2;3] !l;
  Lib.add_to_list ~append:true l 4;
  assert_equal [0;1;2;3;4] !l

let test_lib_filter_out _ =
  assert_equal [1;3;5] (Lib.filter_out (fun x -> x mod 2 = 0) [1;2;3;4;5])

let test_lib_unions _ =
  let r = Lib.unions [[1;2]; [2;3]; [3;4]] in
  assert_equal [1;2;3;4] (List.sort compare r)

let test_lib_foldr2_foldl2 _ =
  assert_equal [1+10; 2+20; 3+30]
    (Lib.foldr2 (fun a b acc -> (a+b)::acc) [] [1;2;3] [10;20;30]);
  assert_equal 66
    (Lib.foldl2 (fun a b acc -> a + b + acc) 0 [1;2;3] [10;20;30]);
  assert_raises (Failure "foldr2")
    (fun () -> Lib.foldr2 (fun _ _ _ -> ()) () [1] [1;2])

let test_lib_compare_with _ =
  let by_len = Lib.compare_with String.length in
  assert_equal 0  (by_len "ab" "cd");
  assert_equal true (by_len "a" "ab" < 0)


(* ===================================================================== *)
(* Tests for Gensym                                                       *)
(* ===================================================================== *)

let test_gensym_basic _ =
  let g = Gensym.create () in
  assert_equal "x1" (Gensym.next g "x");
  assert_equal "x2" (Gensym.next g "x");
  assert_equal "x3" (Gensym.next g "x")

let test_gensym_different_bases _ =
  let g = Gensym.create () in
  assert_equal "a1" (Gensym.next g "a");
  assert_equal "b2" (Gensym.next g "b");
  assert_equal "a3" (Gensym.next g "a")

let test_gensym_independent_generators _ =
  let g1 = Gensym.create () in
  let g2 = Gensym.create () in
  assert_equal "x1" (Gensym.next g1 "x");
  assert_equal "x1" (Gensym.next g2 "x");
  assert_equal "x2" (Gensym.next g1 "x");
  assert_equal "x2" (Gensym.next g2 "x")

let test_gensym_next_not_in _ =
  let g = Gensym.create () in
  let known = fun s -> s = "x1" || s = "x2" in
  (* x1 and x2 are known, so next_not_in should produce x3 *)
  assert_equal "x3" (Gensym.next_not_in g known "x")

let test_gensym_next_not_in_no_conflict _ =
  let g = Gensym.create () in
  let known = fun _ -> false in
  assert_equal "y1" (Gensym.next_not_in g known "y")

let test_gensym_empty_base _ =
  let g = Gensym.create () in
  assert_equal "1" (Gensym.next g "");
  assert_equal "2" (Gensym.next g "")


(* ===================================================================== *)
(* Tests for Ast / Astutil                                                *)
(* ===================================================================== *)

open Ast
open Astutil

let dummy = Ast.dummy_loc

let mk n = { elt = n; loc = dummy }

let test_string_of_ident _ =
  assert_equal "foo"      (string_of_ident (Id "foo"));
  assert_equal "A::B::c"  (string_of_ident (Qualid ("A", ["B"; "c"])));
  assert_equal "M::x"     (string_of_ident (Qualid ("M", ["x"])))

let test_mk_node_get_elts _ =
  let n1 = mk_node dummy 1 in
  let n2 = mk_node dummy 2 in
  let n3 = mk_node dummy 3 in
  assert_equal [1;2;3] (get_elts [n1; n2; n3]);
  assert_equal []      (get_elts [])

let test_string_of_ty _ =
  assert_equal "int"  (string_of_ty (mk (Tctor (Id "int",  []))));
  assert_equal "bool" (string_of_ty (mk (Tctor (Id "bool", []))));
  assert_equal "int array"
    (string_of_ty (mk (Tctor (Id "array", [mk (Tctor (Id "int", []))]))))

let test_equal_ty _ =
  let int_ty  = mk (Tctor (Id "int",  [])) in
  let bool_ty = mk (Tctor (Id "bool", [])) in
  assert_equal true  (equal_ty int_ty  int_ty);
  assert_equal false (equal_ty int_ty  bool_ty);
  assert_equal true  (equal_ty bool_ty bool_ty)

let test_equal_exp_constants _ =
  let c n = mk (Econst (mk (Eint n))) in
  assert_equal true  (equal_exp (c 1) (c 1));
  assert_equal false (equal_exp (c 1) (c 2));
  let t = mk (Econst (mk (Ebool true)))  in
  let f = mk (Econst (mk (Ebool false))) in
  assert_equal true  (equal_exp t t);
  assert_equal false (equal_exp t f)

let test_equal_exp_var _ =
  let x = mk (Evar (Id "x")) in
  let y = mk (Evar (Id "y")) in
  assert_equal true  (equal_exp x x);
  assert_equal false (equal_exp x y)

let test_equal_exp_binop _ =
  let x   = mk (Evar (Id "x")) in
  let y   = mk (Evar (Id "y")) in
  let add = mk (Ebinop (Plus, x, y)) in
  let sub = mk (Ebinop (Minus, x, y)) in
  assert_equal true  (equal_exp add add);
  assert_equal false (equal_exp add sub)

let test_equal_exp_unop _ =
  let x    = mk (Evar (Id "x")) in
  let negx = mk (Eunrop (Uminus, x)) in
  let notx = mk (Eunrop (Not, x)) in
  assert_equal true  (equal_exp negx negx);
  assert_equal false (equal_exp negx notx)

let test_qualify_ident _ =
  assert_equal (Id "x")             (qualify_ident (Id "x") None);
  assert_equal (Qualid ("M", ["x"])) (qualify_ident (Id "x") (Some "M"));
  assert_equal (Qualid ("N", ["M"; "x"]))
    (qualify_ident (Qualid ("M", ["x"])) (Some "N"))

let test_qualify_ty_primitives _ =
  (* Primitive types should not be qualified *)
  let int_t  = mk (Tctor (Id "int",  [])) in
  let bool_t = mk (Tctor (Id "bool", [])) in
  let rgn_t  = mk (Tctor (Id "rgn",  [])) in
  let unit_t = mk (Tctor (Id "unit", [])) in
  assert_equal int_t.elt  (qualify_ty int_t  "M").elt;
  assert_equal bool_t.elt (qualify_ty bool_t "M").elt;
  assert_equal rgn_t.elt  (qualify_ty rgn_t  "M").elt;
  assert_equal unit_t.elt (qualify_ty unit_t "M").elt

let test_qualify_ty_user_type _ =
  let foo_t = mk (Tctor (Id "Foo", [])) in
  let q = qualify_ty foo_t "M" in
  assert_equal (Tctor (Qualid ("M", ["Foo"]), [])) q.elt

let test_is_left_right_value _ =
  let lv = mk (Left  (mk (Evar (Id "x")))) in
  let rv = mk (Right (mk (Evar (Id "y")))) in
  assert_equal true  (is_left_value  lv);
  assert_equal false (is_left_value  rv);
  assert_equal false (is_right_value lv);
  assert_equal true  (is_right_value rv)

let test_is_relation_module _ =
  let bi = mk (Rel_mdl (mk { bimdl_name    = Id "B";
                              bimdl_left_impl  = Id "A";
                              bimdl_right_impl = Id "B";
                              bimdl_elts   = [] })) in
  let ui = mk (Unr_intr (mk { intr_name = Id "I"; intr_elts = [] })) in
  assert_equal true  (is_relation_module bi);
  assert_equal false (is_relation_module ui)

let test_get_program_elt_name _ =
  let idef = mk { intr_name = Id "I"; intr_elts = [] } in
  let mdef = mk { mdl_name  = Id "M"; mdl_interface = Id "I"; mdl_elts = [] } in
  let bdef = mk { bimdl_name = Id "B"; bimdl_left_impl = Id "A";
                  bimdl_right_impl = Id "B"; bimdl_elts = [] } in
  assert_equal (Id "I") (get_program_elt_name (Unr_intr idef));
  assert_equal (Id "M") (get_program_elt_name (Unr_mdl  mdef));
  assert_equal (Id "B") (get_program_elt_name (Rel_mdl  bdef))

let make_idef elts =
  mk { intr_name = Id "I"; intr_elts = elts }

let make_mdef elts =
  mk { mdl_name = Id "M"; mdl_interface = Id "I"; mdl_elts = elts }

let test_interface_methods _ =
  let dummy_ty = mk (Tctor (Id "unit", [])) in
  let decl = mk { meth_name = Id "f"; params = [];
                   result_ty = dummy_ty; result_is_non_null = false;
                   meth_spec = mk [] } in
  let idef = make_idef [mk (Intr_mdecl decl)] in
  assert_equal 1 (List.length (interface_methods idef));
  let idef_no_meths = make_idef [mk (Intr_datagroup [Id "dg"])] in
  assert_equal 0 (List.length (interface_methods idef_no_meths))

let test_interface_classes _ =
  let cdecl = mk { class_name = Id "C"; fields = [] } in
  let idef = make_idef [mk (Intr_cdecl cdecl)] in
  assert_equal 1 (List.length (interface_classes idef));
  let idef_empty = make_idef [] in
  assert_equal 0 (List.length (interface_classes idef_empty))

let test_interface_datagroups _ =
  let idef = make_idef [mk (Intr_datagroup [Id "a"; Id "b"]);
                         mk (Intr_datagroup [Id "c"])] in
  let dgs = interface_datagroups idef in
  assert_equal 3 (List.length dgs);
  assert_equal true (List.mem (Id "a") dgs);
  assert_equal true (List.mem (Id "c") dgs)

let test_module_methods _ =
  let dummy_ty = mk (Tctor (Id "unit", [])) in
  let decl = mk { meth_name = Id "g"; params = [];
                   result_ty = dummy_ty; result_is_non_null = false;
                   meth_spec = mk [] } in
  let mdef_elt = mk (Mdl_mdef (mk (Method (decl, None)))) in
  let mdef = make_mdef [mdef_elt] in
  assert_equal 1 (List.length (module_methods mdef))

let test_module_classes _ =
  let cdecl = mk { class_name = Id "D"; fields = [] } in
  let mdef = make_mdef [mk (Mdl_cdef (mk (Class cdecl)))] in
  assert_equal 1 (List.length (module_classes mdef));
  let mdef_empty = make_mdef [] in
  assert_equal 0 (List.length (module_classes mdef_empty))

let test_equal_formula_basics _ =
  let ftrue  = mk Ftrue in
  let ffalse = mk Ffalse in
  assert_equal true  (equal_formula ftrue  ftrue);
  assert_equal true  (equal_formula ffalse ffalse);
  assert_equal false (equal_formula ftrue  ffalse)

let test_equal_formula_not _ =
  let ftrue = mk Ftrue in
  let nott  = mk (Fnot ftrue) in
  let notf  = mk (Fnot (mk Ffalse)) in
  assert_equal true  (equal_formula nott nott);
  assert_equal false (equal_formula nott notf)

let test_equal_formula_conn _ =
  let ft = mk Ftrue in
  let ff = mk Ffalse in
  let conj = mk (Fconn (Conj, ft, ff)) in
  let disj = mk (Fconn (Disj, ft, ff)) in
  assert_equal true  (equal_formula conj conj);
  assert_equal false (equal_formula conj disj)

let test_equal_atomic_command_skip _ =
  let skip1 = mk Skip in
  let skip2 = mk Skip in
  assert_equal true (equal_atomic_command skip1 skip2)

let test_equal_atomic_command_assign _ =
  let e1 = mk (Econst (mk (Eint 1))) in
  let e2 = mk (Econst (mk (Eint 2))) in
  let a1 = mk (Assign (Id "x", e1)) in
  let a2 = mk (Assign (Id "x", e2)) in
  let a3 = mk (Assign (Id "y", e1)) in
  assert_equal true  (equal_atomic_command a1 a1);
  assert_equal false (equal_atomic_command a1 a2);
  assert_equal false (equal_atomic_command a1 a3)

let test_string_of_modifier _ =
  assert_equal "public"   (string_of_modifier Public);
  assert_equal "ghost"    (string_of_modifier Ghost);
  assert_equal "modscope" (string_of_modifier Modscope)

let test_string_of_loc _ =
  let loc = { loc_fname = "test.rl"; loc_line = 10; loc_range = (3, 7) } in
  assert_equal "test.rl:10:3-7" (string_of_loc loc)


(* ===================================================================== *)
(* Suite assembly                                                          *)
(* ===================================================================== *)

let lib_tests = "Lib" >::: [
  "basic"              >:: test_lib_basic;
  "total_partial"      >:: test_lib_total_partial;
  "check"              >:: test_lib_check;
  "lists_basic"        >:: test_lib_lists_basic;
  "split_at"           >:: test_lib_split_at;
  "take_drop"          >:: test_lib_take_drop;
  "take_while_drop_while" >:: test_lib_take_while_drop_while;
  "no_duplicates"      >:: test_lib_no_duplicates;
  "nub"                >:: test_lib_nub;
  "destutter"          >:: test_lib_destutter;
  "unzip"              >:: test_lib_unzip;
  "interleave"         >:: test_lib_interleave;
  "tabulate_replicate" >:: test_lib_tabulate_replicate;
  "folds"              >:: test_lib_folds;
  "scan"               >:: test_lib_scan;
  "concat_map"         >:: test_lib_concat_map;
  "set_ops"            >:: test_lib_set_ops;
  "ucons"              >:: test_lib_ucons;
  "rev_assoc"          >:: test_lib_rev_assoc;
  "first"              >:: test_lib_first;
  "strings"            >:: test_lib_strings;
  "getchar"            >:: test_lib_getchar;
  "option_monad"       >:: test_lib_option_monad;
  "result_monad"       >:: test_lib_result_monad;
  "fix"                >:: test_lib_fix;
  "add_to_list"        >:: test_lib_add_to_list;
  "filter_out"         >:: test_lib_filter_out;
  "unions"             >:: test_lib_unions;
  "foldr2_foldl2"      >:: test_lib_foldr2_foldl2;
  "compare_with"       >:: test_lib_compare_with;
]

let gensym_tests = "Gensym" >::: [
  "basic"              >:: test_gensym_basic;
  "different_bases"    >:: test_gensym_different_bases;
  "independent"        >:: test_gensym_independent_generators;
  "next_not_in"        >:: test_gensym_next_not_in;
  "next_not_in_no_conflict" >:: test_gensym_next_not_in_no_conflict;
  "empty_base"         >:: test_gensym_empty_base;
]

let astutil_tests = "Astutil" >::: [
  "string_of_ident"        >:: test_string_of_ident;
  "mk_node_get_elts"       >:: test_mk_node_get_elts;
  "string_of_ty"           >:: test_string_of_ty;
  "equal_ty"               >:: test_equal_ty;
  "equal_exp_constants"    >:: test_equal_exp_constants;
  "equal_exp_var"          >:: test_equal_exp_var;
  "equal_exp_binop"        >:: test_equal_exp_binop;
  "equal_exp_unop"         >:: test_equal_exp_unop;
  "qualify_ident"          >:: test_qualify_ident;
  "qualify_ty_primitives"  >:: test_qualify_ty_primitives;
  "qualify_ty_user_type"   >:: test_qualify_ty_user_type;
  "is_left_right_value"    >:: test_is_left_right_value;
  "is_relation_module"     >:: test_is_relation_module;
  "get_program_elt_name"   >:: test_get_program_elt_name;
  "interface_methods"      >:: test_interface_methods;
  "interface_classes"      >:: test_interface_classes;
  "interface_datagroups"   >:: test_interface_datagroups;
  "module_methods"         >:: test_module_methods;
  "module_classes"         >:: test_module_classes;
  "equal_formula_basics"   >:: test_equal_formula_basics;
  "equal_formula_not"      >:: test_equal_formula_not;
  "equal_formula_conn"     >:: test_equal_formula_conn;
  "equal_atomic_cmd_skip"  >:: test_equal_atomic_command_skip;
  "equal_atomic_cmd_assign">:: test_equal_atomic_command_assign;
  "string_of_modifier"     >:: test_string_of_modifier;
  "string_of_loc"          >:: test_string_of_loc;
]

let () =
  run_test_tt_main ("RelRL Unit Tests" >::: [
    lib_tests;
    gensym_tests;
    astutil_tests;
  ])
