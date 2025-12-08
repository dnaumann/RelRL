/*

// A program that does not leak high-security state.

expected: valid;

forall: nonleak[1];
exists: nonleak[2];

pre:  (= nonleak!1!low  nonleak!2!low);
post: (and
        (= nonleak!1!low nonleak!2!low)
        (= nonleak!1!ret nonleak!2!ret));

fun nonleak(high, low) {
  x   := low + high;
  ret := x - high;
  return ret;
}

*/

var low_1, low_2, high_1, high_2 : int;

procedure biprog () returns (ret_1, ret_2: int)
  requires low_1 == low_2;
  ensures low_1 == low_2;
  ensures ret_1 == ret_2;
{
    var x1, x2: int;

    x1 := low_1 + high_1; x2 := low_2 + high_2;

    ret_1 := x1 - high_1; ret_2 := x2 - high_2;
}

