/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/api-refinement/loop-nonrefinement.imp
// A nonrefinement involving a simple loop.

*/

// should not verify
procedure loopNonrefinement () returns (sum: int, sum': int)
          requires true;
          ensures sum == sum';
{

var r: int; 
var r': int;

sum := 0; 
sum' := 0;

while (sum <= 100 && sum' <= 100)
   invariant sum == sum'; 
  {
    // left program
    havoc r; assume 0 <= r && r < 11;
    sum := sum + r;

   // inserted by chk
   assert (exists v: int :: 0 <= v && v < 10 && r == v);

   // right program
   havoc r'; assume 0 <= r' && r' < 10;
   // filter 
   assume r == r'; 

   // right program 
   sum' := sum' + r';

  }
} 
