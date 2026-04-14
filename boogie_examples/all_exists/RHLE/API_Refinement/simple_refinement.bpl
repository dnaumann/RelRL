/*

https://github.com/rcdickerson/rhle-benchmarks/blob/main/api-refinement/simple-refinement.imp

// A program together with a valid refinement.

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


