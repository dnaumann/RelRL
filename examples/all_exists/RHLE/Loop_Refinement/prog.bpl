
// this should and does verify
procedure loopRefinement () returns (sum: int, sum': int)
          requires true;
          ensures sum == sum';
{
// lockstep loop alignment; don't bother with alignment conditions 
// The RHLE code uses variants for both left and right loops; this is unnecessary for lockstep alignment!

var r: int; 
var r': int;

sum := 0; 
sum' := 0;

while (sum <= 100 && sum' <= 100)
   invariant sum == sum'; 
  {
    // left program
    havoc r; assume 0 <= r && r < 10 && r mod 2 == 1;
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
