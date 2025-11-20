interface I =

  import theory List3
  extern type intList with default = nil
  extern listNth3(int, intList): int
  extern listLength(intList): int
  extern is_sorted3(intList) : bool
  extern is_permutation3(intList, intList) : bool
  extern add3(intList): intList
  extern cons(int, intList): intList

  meth prog (l:intList) : intList



  lemma permutation3_is_transitive: forall l1: intList, l2: intList, l3: intList .
    is_permutation3(l1, l2) -> is_permutation3(l2, l3) -> is_permutation3(l2, l3) 

  lemma permutation3_is_reflexive: forall l1: intList, l2: intList .
    is_permutation3(l1, l2) -> is_permutation3(l2, l1)

  lemma list3_listNth3_form: forall l: intList . 
    listLength(l) = 3 <-> l = cons(listNth3(0, l), cons(listNth3(1, l), cons( listNth3(2, l), nil)))

  lemma sort_perm_unique : forall l1: intList, l2: intList .
    is_sorted3(l1) -> is_permutation3(l1, l2) -> is_sorted3(l2) ->  l1 = l2


end

module A : I =
  meth prog (l:intList) : intList
end

module B : I =
  meth prog (l:intList) : intList
end


bimodule FREL (A | B) =


  import theory List3

  meth prog (l: intList|  l: intList) : (intList | intList)
  requires {Both (listLength(l) = 3)}
  requires {   l  =:=  l  }
  ensures { result =:= result   }
 =
    Var shuffle_ret: intList | sort_ret : intList in
    Var | choice_list : intList in 

     /* left program calls shuffle with universal spec */
    (havoc shuffle_ret; assume { is_permutation3(l, shuffle_ret) } | skip);

     /* right program calls sort with existential spec instantiated with shuffle_ret */
    (skip | assume { is_sorted3(choice_list) });
    (skip | assume { is_permutation3(l, choice_list) });
    HavocR sort_ret { [> sort_ret = choice_list |> };
     (l := shuffle_ret | l := sort_ret);
     
     |_ l := add3(l) _|;  

     |_ result := l _|; 

end

