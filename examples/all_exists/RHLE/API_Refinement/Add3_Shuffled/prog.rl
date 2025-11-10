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
end

module A : I =
  meth prog (l:intList) : intList
end

module B : I =
  meth prog (l:intList) : intList
end


bimodule FREL (A | B) =

  import theory List3

  predicate equals3_bipred (l: intList | l: intList) =
      let fst | fst = listNth(0, l) | listNth(0, l) in let snd | snd = listNth(1, l) | listNth(1, l) in let third | third = listNth(2, l) | listNth(2, l) in fst =:= fst /\ snd =:= snd /\ third =:= third
 /* should not and does not verify */
  meth prog (l: intList|  l: intList) : (intList | intList)
  requires {Both (listLength(l) = 3)}
  requires { equals3_bipred(  l  |  l ) }
  ensures { equals3_bipred(  result | result  ) }
 =

    Var shuffle_ret: intList | sort_ret : intList in
    Var | choice_list : intList in 

     /* left program calls shuffle with universal spec */
    (havoc shuffle_ret; assume { is_permutation3(l, shuffle_ret) } | skip);

     /* right program calls sort with existential spec instantiated with shuffle_ret */
    (skip | assume { is_sorted3(choice_list) });
    (skip | assume { is_permutation3(l, choice_list) });
    HavocR sort_ret { [> equals3(sort_ret, choice_list) |> };
     (l := shuffle_ret | l := sort_ret);
     
     |_ l := add3_3(l) _|;  

     |_ result := l _|; 

end