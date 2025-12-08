/*

// A program with a straightforward leak of high-security state.

expected: invalid;

forall: leak[1];
exists: leak[2];

pre:  (= leak!1!low  leak!2!low);
post: (and
        (= leak!1!low leak!2!low)
        (= leak!1!ret leak!2!ret));

fun leak(high, low) {
  ret := high + low;
  return ret;
}

*/


var low_1, low_2, high_1, high_2 : int;

// should not and does not verify
procedure biprog () returns (ret_1, ret_2: int)
  requires low_1 == low_2;
  ensures low_1 == low_2;
  ensures ret_1 == ret_2;
{
    ret_1 := high_1 + low_1;
    ret_2 := high_2 + low_2;
}