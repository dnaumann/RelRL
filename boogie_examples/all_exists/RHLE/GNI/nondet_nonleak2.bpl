/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/gni/nondet-nonleak2.imp
*/


var low_1, low_2, high_1, high_2 : int;

procedure skip () returns ();

// verifies
procedure biprog () returns ()
  requires low_1 == low_2;
  ensures low_1 == low_2;
  modifies low_1, low_2, high_1, high_2;
{
  var flipcoin_ret1, flipcoin_ret2: int;
  var choicevar : int;

  if (low_1 < high_1) 
  {
    low_1 := 0;
  }
  else
  {
    low_1 := 1;
  }

  if (low_2 < high_2) 
  {
    low_2 := 0;
  }
  else
  {
    low_2 := 1;
  }

  // left program calls with universal spec
  havoc flipcoin_ret1; assume (0 == flipcoin_ret1 || flipcoin_ret1 == 1);

  // Picking choice variable instantiation
  if (low_1 == low_2)
  {
     choicevar := flipcoin_ret1;
  }
  else
  {
    choicevar := 1 - flipcoin_ret1;
  }

  // right program calls with existential spec with choicevar
  // assume ( (0 == choicevar || choicevar == 1));
  assert (exists v: int ::  v == choicevar);
  havoc flipcoin_ret2; 
  assume (flipcoin_ret2 == choicevar);
  

  if (flipcoin_ret1 == 0)
  {
    low_1 := 1 - low_1;
  }
  
  if (flipcoin_ret2 == 0)
  {
    low_2 := 1 - low_2;
  }

}