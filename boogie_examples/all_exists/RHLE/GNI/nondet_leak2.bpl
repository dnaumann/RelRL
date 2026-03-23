/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/gni/nondet-leak2.imp

*/

var low_1, low_2, high_1, high_2 : int;

procedure skip () returns ();

// should not and does not verify
procedure biprog () returns ()
  requires low_1 == low_2;
  ensures low_1 == low_2;
  modifies low_1, low_2, high_1, high_2;
{
  var flipcoin_ret1, flipcoin_ret2: int;
  var choice_var: int;

  // left program calls with universal spec
  havoc flipcoin_ret1; assume (0 == flipcoin_ret1 || flipcoin_ret1 == 1);

  // right program calls with existential spec with choicevar instantiated with flipcoin_ret1
  choice_var := flipcoin_ret1;
  assert (exists v: int ::  v == choice_var);
  havoc flipcoin_ret2; 
  assume (flipcoin_ret2 == flipcoin_ret1);
  
  if (flipcoin_ret1 == 0)
  {
    low_1 := high_1 + low_1;
  }
  else
  {
    call skip();
  }

  if (flipcoin_ret2 == 0)
  {
    low_2 := high_2 + low_2;
  }
  else
  {
    call skip();
  }

}