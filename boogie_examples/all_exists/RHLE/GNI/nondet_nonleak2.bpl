/*
// A program that never leaks high-
// security state.

expected: valid;

forall: run[1];
exists: run[2];

pre:  (= run!1!low run!2!low);
post: (= run!1!low run!2!low);

aspecs:
  flipCoin() {
    pre:  true;
    post: (or (= ret! 0) (= ret! 1));
  }

especs:
  flipCoin() {
    choiceVars: n;
    pre:  (or (= n 0) (= n 1));
    post: (= ret! n);
  }

fun run(high, low) {
  if (low < high) then
    low := 0;
  else
    low := 1;
  endif

  flip := flipCoin();
  if (flip == 0) then
    low := 1 - low;  // Flip low.
  endif
  return low;
}
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