/*

// A refinement involving a simple conditional.

expected: valid;

forall: refinement;
exists: original;

pre:  true;
post: (= original!ret refinement!ret);

aspecs:
  flipCoin() {
    pre: true;
    post: (or (= ret! 0) (= ret! 1));
  }

especs:
  flipCoin() {
    choiceVars: n;
    pre: (or (= n 0) (= n 1));
    post: (= ret! n);
  }

fun original() {
  r := flipCoin();
  if (r == 0) then
    ret := 10;
  else
    ret := 20;
  endif
  return ret;
}

fun refinement() {
  r := flipCoin();
  if (r == 0) then
    ret := 20;
  else
    ret := 10;
  endif
  return ret;
}

*/


function inst (v: int) returns (bool) {true}

procedure biprog () returns (o_ref: int, o_orig: int)
  requires true;
  ensures o_ref == o_orig;
{
  var choice_var: int;
  var flipret_ref : int;
  var flipret_orig : int;

  havoc flipret_ref;
  assume flipret_ref == 0 || flipret_ref == 1; // universal spec
  
  if (flipret_ref == 0) 
  {  o_ref := 10;}
  else
  {  o_ref := 20;}

  // existential spec instantiated with opposite of flipret_ref
  choice_var := 1 - flipret_ref;
  assert (exists v: int ::  (v == choice_var));
  havoc flipret_orig;
  assume (choice_var == flipret_orig); 


  if (flipret_orig == 0)
  { 
     o_orig := 20;
  }
  else
  {  o_orig := 10;
  
  }
}