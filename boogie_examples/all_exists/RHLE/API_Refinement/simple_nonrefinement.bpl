/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/api-refinement/simple-nonrefinement.imp
// A program together with an invalid refinement.

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
