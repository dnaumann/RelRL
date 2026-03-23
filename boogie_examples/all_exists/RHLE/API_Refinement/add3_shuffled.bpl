/* https://github.com/rcdickerson/rhle-benchmarks/blob/main/api-refinement/add3-shuffled.imp

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