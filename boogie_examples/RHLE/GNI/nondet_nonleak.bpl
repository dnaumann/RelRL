/*

// A program which has an unreachable execution path that would
// leak high-security state.

expected: valid;

forall: nonleak[1];
exists: nonleak[2];

pre: (= nonleak!1!low nonleak!2!low);
post: (and
        (= nonleak!1!low nonleak!2!low)
        (= nonleak!1!ret nonleak!2!ret));

aspecs:
  randInt() {
    pre: true;
    post: (and (>= ret! 0) (< ret! 100));
  }

especs:
  randInt() {
    choiceVars: n;
    pre: (and (>= n 0) (< n 100));
    post: (= ret! n);
  }

fun nonleak(high, low) {
  r := randInt();
  if (r == 5000) then
    ret := high + low;
  else
    ret := low;
  endif
  return ret;
}

*/

var low_1, low_2, high_1, high_2 : int;

procedure biprog () returns (ret_1, ret_2: int)
  requires low_1 == low_2;
  ensures low_1 == low_2;
  ensures ret_1 == ret_2;
{
  var randint_ret1, randint_ret2: int;
  var choice_var: int;

  // left program calls with universal spec
  havoc randint_ret1; assume (0 <= randint_ret1 && randint_ret1 < 100);

  // right program calls with existential spec with choicevar instantiated with randint_ret1
  choice_var := randint_ret1;
  assert (exists v: int ::  v == choice_var);
  havoc randint_ret2; 
  assume (randint_ret2 == choice_var);
  
  if (randint_ret1 == 5000)
  {
    ret_1 := high_1 + low_1;
  }
  else
  {
    ret_1 := low_1;
  }

  if (randint_ret2 == 5000)
  {
    ret_2 := high_2 + low_2;
  }
  else
  {
    ret_2 := low_2;
  }
}