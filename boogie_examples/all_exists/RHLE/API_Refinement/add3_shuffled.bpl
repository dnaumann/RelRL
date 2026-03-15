/*

expected: invalid;

forall: refinement;
exists: original;

pre:  (and
        (= original!list_0 refinement!list_0)
        (= original!list_1 refinement!list_1)
        (= original!list_2 refinement!list_2));
post: (and
        (= original!ret_0 refinement!ret_0)
        (= original!ret_1 refinement!ret_1)
        (= original!ret_2 refinement!ret_2));

aspecs:
  shuffle(list[3]) {
    post: (or (and (= ret!0 list_0)
                   (= ret!1 list_1)
                   (= ret!2 list_2))
               (and (= ret!0 list_0)
                    (= ret!1 list_2)
                    (= ret!2 list_1))
               (and (= ret!0 list_1)
                    (= ret!1 list_0)
                    (= ret!2 list_2))
               (and (= ret!0 list_1)
                    (= ret!1 list_2)
                    (= ret!2 list_0))
               (and (= ret!0 list_2)
                    (= ret!1 list_0)
                    (= ret!2 list_1))
               (and (= ret!0 list_2)
                    (= ret!1 list_1)
                    (= ret!2 list_0)));
  }

especs:
  sort(list[3]) {
    choiceVars: n0, n1, n2;
    pre: (and (<= n0 n1)
              (<= n1 n2)
              (or (and (= n0 list_0)
                       (= n1 list_1)
                       (= n2 list_2))
                  (and (= n0 list_0)
                       (= n1 list_2)
                       (= n2 list_1))
                  (and (= n0 list_1)
                       (= n1 list_0)
                       (= n2 list_2))
                  (and (= n0 list_1)
                       (= n1 list_2)
                       (= n2 list_0))
                  (and (= n0 list_2)
                       (= n1 list_0)
                       (= n2 list_1))
                  (and (= n0 list_2)
                       (= n1 list_1)
                       (= n2 list_0))));
    post: (and (= ret!0 n0)
               (= ret!1 n1)
               (= ret!2 n2));
  }

// The original program sorts the list then adds three
// to each value.
fun original(list[3]) {
  sorted[3] := sort(list[3]);
  ret_0 := sorted_0 + 3;
  ret_1 := sorted_1 + 3;
  ret_2 := sorted_2 + 3;
  return ret;
}

// The refinement program shuffles the list to some
// arbitrary permutation then adds three to each value.
fun refinement(list[3]) {
  shuffled[3] := shuffle(list[3]);
  ret_0 := shuffled_0 + 3;
  ret_1 := shuffled_1 + 3;
  ret_2 := shuffled_2 + 3;
  return ret;
}

*/

type list = [int]int;

var list_1: list; var list_2: list;

function equals3 (lhs, rhs: list) returns (bool){
     (lhs[0] == rhs[0] && lhs[1] == rhs[1] && lhs[2] == rhs[2])
}


function is_sorted3 (l: list) returns (bool)
{
     (l[0] <= l[1] && l[1] <= l[2])     
} 

function is_permutation3(l, r: list) returns (bool)
{
    (((l[0] == r[0]) &&  (l[1] == r[1]) && (l[2] == r[2])) ||
     ((l[0] == r[0]) &&  (l[1] == r[2]) && (l[2] == r[1])) ||
     ((l[0] == r[1]) &&  (l[1] == r[0]) && (l[2] == r[2])) ||
     ((l[0] == r[1]) &&  (l[1] == r[2]) && (l[2] == r[0])) ||
     ((l[0] == r[2]) &&  (l[1] == r[0]) && (l[2] == r[1])) ||
     ((l[0] == r[2]) &&  (l[1] == r[1]) && (l[2] == r[0])))
}

axiom (forall l1, l2: list :: equals3(l1, l2) ==> is_permutation3(l1, l2)) ;

// should not and does not verify
procedure biprog () returns ()
  requires equals3(list_1, list_2);
  ensures equals3(list_1, list_2);
  modifies list_1, list_2;
{
     var shuffle_ret, sort_ret, choice_list : list;

     // left program calls shuffle with universal spec
     havoc shuffle_ret; assume (is_permutation3(list_1, shuffle_ret));

     // right program calls sort with existential spec instantiated with choice_list.
     assume (is_sorted3(choice_list));
     assume (is_permutation3(list_2, choice_list));
     assert (exists v: list :: v == choice_list); //inserted by chk
     havoc sort_ret;
     assume (equals3(sort_ret, choice_list));
     list_1 := shuffle_ret;  list_2 := sort_ret;
     
     list_1 := list_1[0 := list_1[0] + 3]; 
     list_2 := list_2[0 := list_2[0] + 3];  
     list_1 := list_1[1 := list_1[1] + 3];  
     list_2 := list_2[1 := list_2[1] + 3];  
     list_1 := list_1[2 := list_1[2] + 3];  
     list_2 := list_2[2 := list_2[2] + 3];  

}