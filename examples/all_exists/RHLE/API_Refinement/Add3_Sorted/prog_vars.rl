interface I =
  class List3 {l1: int; l2: int; l3: int; }
  
  meth prog (l: List3) : List3 
    effects { rd l; rw {l}`any }


  predicate is_sorted3 (l: List3) =
      let fst = l.l1 in let snd = l.l2 in let third = l.l3 in fst <= snd /\ snd <= third


 predicate is_permutation3 (l1: List3, l2: List3)  =
    let fst1 = l1.l1 in 
    let fst2 = l2.l1 in
    let snd1 = l1.l2 in 
    let snd2 = l2.l2 in
    let third1 = l1.l3 in 
    let third2 = l2.l3 in
    
    (((fst1 = fst2) /\  (snd1 = snd2) /\ (third1 = third2)) \/
     ((fst1 = fst2) /\  (snd1 = third2) /\ (third1 = snd2)) \/
     ((fst1 = snd2) /\  (snd1 = fst2) /\ (third1 = third2)) \/
     ((fst1 = snd2) /\  (snd1 = third2) /\ (third1 = fst2)) \/
     ((fst1 = third2) /\  (snd1 = fst2) /\ (third1 = snd2)) \/
     ((fst1 = third2) /\  (snd1 = snd2) /\ (third1 = fst2)))

predicate equals3 (l1: List3, l2: List3)  =
    let fst1 = l1.l1 in 
    let fst2 = l2.l1 in
    let snd1 = l1.l2 in 
    let snd2 = l2.l2 in
    let third1 = l1.l3 in 
    let third2 = l2.l3 in

    (fst1 = fst2 /\ snd1 = snd2 /\ third1 = third2)

end

module A : I =
  class List3 {l1: int; l2: int; l3: int; }
  
  meth prog (l: List3) : List3 
    effects { rd l; rw {l}`any }

end

module B : I =
  class List3 {l1: int; l2: int; l3: int; }
  
  meth prog (l: List3) : List3 
    effects { rd l; rw {l}`any }

end


bimodule FREL (A | B) =

  predicate equals3_bipred  (l: List3 | l: List3) =
      let fst | fst = l.l1 | l.l1 in let snd | snd = l.l2 | l.l2 in let third | third = l.l3 | l.l3 in fst =:= fst /\ snd =:= snd /\ third =:= third


  meth prog (l : List3 |  l: List3) : (List3 | List3)
  requires { equals3_bipred(  l  |  l ) }
  ensures { equals3_bipred(  result | result  ) }
  effects {rd l; rw {l}`any | rd l; rw {l}`any}
 =

    Var sort_ret: List3 | shuffle_ret : List3 in
    Var | choice_list : List3 in 

     /* left program calls shuffle with universal spec */
    (havoc sort_ret; assume { is_permutation3(l, sort_ret) } | skip);

     /* right program calls sort with existential spec instantiated with sort_ret */
    (skip | assume { is_sorted3(choice_list) });
    (skip | assume { is_permutation3(l, choice_list) });
    HavocR shuffle_ret { [> equals3(shuffle_ret, choice_list) |> };
    /* Assert { equals3_bipred(sort_ret | shuffle_ret) }; */

     (l := sort_ret | l := shuffle_ret);
     
     Var temp: int | temp: int in

     |_  temp := l.l1 _|;  
     |_  l.l1 := temp + 3 _|;  
     |_  temp := l.l2 _|;  
     |_  l.l2 := temp + 3 _|;  
     |_  temp := l.l3 _|;  
     |_  l.l3 := temp + 3 _|;  

     |_ result := l _|; 

end