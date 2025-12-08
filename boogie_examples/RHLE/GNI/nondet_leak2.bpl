/*

// A program that sometimes (but not
// always) leaks high-security state.

expected: invalid;

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
  flip := flipCoin();
  if (flip == 0) then
    low := high + low;
  else
    skip;
  endif
  return low;
}

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