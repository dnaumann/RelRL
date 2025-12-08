/*

// Dropping a sort guarantee from an API is OK when
// the caller performs some operation that doesn't
// care about list order.

expected: valid;

forall: refinement;
exists: original;

pre: (or
       (and (= original!list_0 refinement!list_0)
            (= original!list_1 refinement!list_1)
            (= original!list_2 refinement!list_2))
       (and (= original!list_0 refinement!list_0)
            (= original!list_1 refinement!list_2)
            (= original!list_2 refinement!list_1))
       (and (= original!list_0 refinement!list_1)
            (= original!list_1 refinement!list_0)
            (= original!list_2 refinement!list_2))
       (and (= original!list_0 refinement!list_1)
            (= original!list_1 refinement!list_2)
            (= original!list_2 refinement!list_0))
       (and (= original!list_0 refinement!list_2)
            (= original!list_1 refinement!list_0)
            (= original!list_2 refinement!list_1))
       (and (= original!list_0 refinement!list_2)
            (= original!list_1 refinement!list_1)
            (= original!list_2 refinement!list_0)));
post: (= original!sum refinement!sum);

// The original API call guarantees an ordered list.
// The refinement makes no guarantees. This is OK
// because the sum of the list is the same regardless
// of ordering.

aspecs:
  refinedGetValues() {
    pre: true;
    post: (and (= ret!0 ret!0)
               (= ret!1 ret!1)
               (= ret!2 ret!2));
               // TODO: Annotation for specifying return
               // values when post is trivial.
  }

especs:
  originalGetValues() {
    choiceVars: n0, n1, n2;
    pre: (and (<= n0 n1) (<= n1 n2));
    post: (and (= ret!0 n0) (= ret!1 n1) (= ret!2 n2));
  }

fun original() {
   list[3] := originalGetValues();
   sum := list_0 + list_1 + list_2;
   return sum;
}

fun refinement() {
   list[3] := refinedGetValues();
   sum := list_0 + list_1 + list_2;
   return sum;
}

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