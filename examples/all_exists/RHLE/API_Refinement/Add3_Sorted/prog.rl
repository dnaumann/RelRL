interface I =

  import theory List3
  extern type intList with default = nil
  extern listNth(int, intList): int
  extern listLength(intList): int
  extern is_sorted3(intList) : bool
  extern is_permutation3(intList, intList) : bool
  extern equals3(intList, intList) : bool
  extern add3_3(intList): intList

  meth prog (l:intList) : intList


  lemma add3_preserves_equals3 : forall l1: intList, l2: intList .
    equals3(l1, l2) -> equals3(add3_3(l1), add3_3(l2))
end

module A : I =
  meth prog (l:intList) : intList
end

module B : I =
  meth prog (l:intList) : intList
end


bimodule FREL (A | B) =


  import theory List3

  predicate equals3_bipred  (l: intList | l: intList) =
      let fst | fst = listNth(0, l) | listNth(0, l) in let snd | snd = listNth(1, l) | listNth(1, l) in let third | third = listNth(2, l) | listNth(2, l) in fst =:= fst /\ snd =:= snd /\ third =:= third

  meth prog (l: intList|  l: intList) : (intList | intList)
  requires {Both (listLength(l) = 3)}
  requires { equals3_bipred(  l  |  l ) }
  ensures { equals3_bipred(  result | result  ) }
 =

    Var sort_ret: intList | shuffle_ret : intList in
    Var | choice_list : intList in 

     /* left program calls shuffle with universal spec */
    (havoc sort_ret; assume { is_permutation3(l, sort_ret) } | skip);

     /* right program calls sort with existential spec instantiated with sort_ret */
    (skip | assume { is_sorted3(choice_list) });
    (skip | assume { is_permutation3(l, choice_list) });
    HavocR shuffle_ret { [> equals3(shuffle_ret, choice_list) |> };
    Assert { equals3_bipred(sort_ret | shuffle_ret) };

     (l := sort_ret | l := shuffle_ret);
     
     |_ l := add3_3(l) _|;  

     |_ result := l _|; 

end