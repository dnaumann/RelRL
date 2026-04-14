/* https://github.com/rcdickerson/rhle-benchmarks/blob/main/api-refinement/add3-sorted.imp

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
procedure biprog () returns ()
  requires equals3(list_1, list_2);
  ensures equals3(list_1, list_2);
  modifies list_1, list_2;
{
     var shuffle_ret, sort_ret, choice_list : list;

     // left program calls shuffle with universal spec
     havoc sort_ret; assume (is_permutation3(list_1, sort_ret) && is_sorted3(sort_ret));

     // right program calls shuffle with existential spec instantiated choice list.

     assume (is_permutation3(list_2, choice_list) && is_sorted3(choice_list));
     assert (exists v: list :: v == choice_list); //inserted by chk
     havoc shuffle_ret; 
     assume (shuffle_ret == choice_list);

     list_1 := sort_ret;  list_2 := shuffle_ret;
     
     list_1 := list_1[0 := list_1[0] + 3];  
     list_1 := list_1[1 := list_1[1] + 3];  
     list_1 := list_1[2 := list_1[2] + 3];  
     list_2 := list_2[0 := list_2[0] + 3];  
     list_2 := list_2[1 := list_2[1] + 3];  
     list_2 := list_2[2 := list_2[2] + 3];  
}