/*

// A program together with an invalid refinement.

expected: invalid;

forall: refinement;
exists: original;

post: (= original!x refinement!x);

aspecs:
  refinedRand() {
      pre:  true;
      post: (and (>= ret! 0) (< ret! 25));
  }

especs:
  originalRand() {
      choiceVars: n;
      pre:  (and (>= n 0) (< n 20));
      post: (= ret! n);
  }

fun original() {
  x := originalRand();
  return x;
}

fun refinement() {
  x := refinedRand();
  return x;
}

*/

// should and does fail
procedure simpleNonRefinement () returns (zL: int, zR: int)
          requires true;
          ensures zL == zR;
{
// left program
havoc zL; assume 0 <= zL && zL < 25;  

// inserted by chk -- should fail 
assert (exists v: int :: 0 <= v && v < 20
       && zL == v); 

// right program
havoc zR; assume 0 <= zR && zR < 20;

// filter 
assume zL == zR; 
} 
