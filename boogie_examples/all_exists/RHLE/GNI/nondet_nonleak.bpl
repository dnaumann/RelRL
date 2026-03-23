/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/gni/nondet-nonleak.imp
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