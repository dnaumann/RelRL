/*

// A program together with a valid refinement.

expected: valid;

forall: refinement;
exists: original;

post: (= original!x refinement!x);

aspecs:
  refinedRand() {
      pre:  true;
      post: (and (>= ret! 0) (< ret! 20) (= (mod ret! 2) 1));
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


/* Our version doesn't use procedures and the specs don't use choice vars. 
   It's a little beyond our language; uses havoc-such-that. */

procedure simpleRefinement () returns (zL: int, zR: int)
          requires true;
          ensures zL == zR;
{
// left program
havoc zL; assume 0 <= zL && zL < 20 && zL mod 2 == 1;  // havoc such that 

// inserted by chk (extended to havoc-such-that) -- should succeed 
assert (exists v: int :: 0 <= v && v < 20 
       && zL == v); 

// right program
havoc zR; assume 0 <= zR && zR < 20;

// filter 
assume zL == zR; 
} 


