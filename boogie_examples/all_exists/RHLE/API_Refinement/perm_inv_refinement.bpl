/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/api-refinement/perm-inv-refinement.imp

*/


type list = [int]int;

var list_1: list; var list_2: list;

function equals3 (lhs, rhs: list) returns (bool);

axiom (forall l1, l2: list :: equals3(l1, l2) <==> 
               (l1[0] == l2[0] && l1[1] == l2[1] && l1[2] == l2[2]));


function is_sorted3 (l: list) returns (bool);

axiom (forall l :list :: is_sorted3(l) <==> (l[0] <= l[1] && l[1] <= l[2]));

function is_permutation3(l, r: list) returns (bool)
{
    (((l[0] == r[0]) &&  (l[1] == r[1]) && (l[2] == r[2])) ||
     ((l[0] == r[0]) &&  (l[1] == r[2]) && (l[2] == r[1])) ||
     ((l[0] == r[1]) &&  (l[1] == r[0]) && (l[2] == r[2])) ||
     ((l[0] == r[1]) &&  (l[1] == r[2]) && (l[2] == r[0])) ||
     ((l[0] == r[2]) &&  (l[1] == r[0]) && (l[2] == r[1])) ||
     ((l[0] == r[2]) &&  (l[1] == r[1]) && (l[2] == r[0])))
}

// verifies
procedure biprog () returns (sum_1, sum_2: int)
  requires is_permutation3(list_1, list_2);
  ensures sum_1 == sum_2;
  modifies list_1, list_2;
{
     var refinedGetValues_ret, originalGetValues_ret, choice_list : list;

     // left program calls shuffle with universal spec
     havoc refinedGetValues_ret; 
     assume (refinedGetValues_ret == list_1);

     // right program calls shuffle with existential spec instantiated with refinedGetValues_ret.

     assume (is_permutation3(refinedGetValues_ret, choice_list));
     assume (is_sorted3(choice_list));
     assert (exists v: list :: v == choice_list); //inserted by chk
     havoc originalGetValues_ret;
     assume (originalGetValues_ret == choice_list);

     list_1 := refinedGetValues_ret;  list_2 := originalGetValues_ret;
     
     sum_1 := list_1[0] + list_1[1] + list_1[2];
     sum_2 := list_2[0] + list_2[1] + list_2[2];

}