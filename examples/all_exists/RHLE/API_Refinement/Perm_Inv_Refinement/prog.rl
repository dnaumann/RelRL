interface I =

  import theory List3
  extern type intList with default = nil
  extern listNth3(int, intList): int
  extern listLength(intList): int
  extern is_sorted3(intList) : bool
  extern is_permutation3(intList, intList) : bool
  extern sum(intList): int
  extern cons(int, intList): intList

  meth prog (l:intList) : int



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
  meth prog (l:intList) : int
end

module B : I =
  meth prog (l:intList) : int
end


bimodule FREL (A | B) =


  import theory List3

  predicate is_permutation3_bipred (l: intList | l: intList) =
    let fst | fst = listNth3(0, l) | listNth3(0, l) in
    let snd | snd = listNth3(1, l) | listNth3(1, l) in
    let third | third = listNth3(2, l) | listNth3(2, l) in

    Both (listLength(l) = 3) /\ 
    ((([< fst <] = [> fst >]) /\  ([< snd <] = [> snd >]) /\ ([< third <] = [> third >])) \/
     (([< fst <] = [> fst >]) /\  ([< snd <] = [> third >]) /\ ([< third <] = [> snd >])) \/
     (([< fst <] = [> snd >]) /\  ([< snd <] = [> fst >]) /\ ([< third <] = [> third >])) \/
     (([< fst <] = [> snd >]) /\  ([< snd <] = [> third >]) /\ ([< third <] = [> fst >])) \/
     (([< fst <] = [> third >]) /\  ([< snd <] = [> fst >]) /\ ([< third <] = [> snd >])) \/
     (([< fst <] = [> third >]) /\  ([< snd <] = [> snd >]) /\ ([< third <] = [> fst >])))

  meth prog (l: intList|  l: intList) : (int | int)
  requires { is_permutation3_bipred(  l | l  ) }
  ensures { result =:= result }
 =

    Var refinedGetValues_ret: intList | originalGetValues_ret : intList in
    Var | choice_list : intList in 

     /* left program calls shuffle with universal spec */
    (havoc refinedGetValues_ret; assume {is_permutation3(refinedGetValues_ret, l)}| skip);

     /* right program calls sort with existential spec instantiated with refinedGetValues_ret */
    (skip | assume { is_sorted3(choice_list) });
    (skip | assume { is_permutation3(l, choice_list) });
    HavocR originalGetValues_ret { [> originalGetValues_ret = choice_list |> };
     (l := refinedGetValues_ret | l := originalGetValues_ret);
     
     |_ result := sum(l) _|; 
end