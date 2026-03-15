/*

// A refinement involving a simple loop.

expected: valid;

forall: refinement;
exists: original;

post: (= original!sum refinement!sum);

aspecs:
  randEven() {
    post: (and (<= 0 ret!) (< ret! 10)
               (= (mod ret! 2) 0));
  }

  rand() {
    post: (and (<= 0 ret!) (< ret! 10));
  }

especs:
  rand() {
    choiceVars: n;
    pre:  (and (<= 0 n) (< n 10));
    post: (= ret! n);
  }

fun original() {
  sum := 0;
  while (sum <= 100) do
    @inv { (= original!sum refinement!sum) }
    @var { (+ 200 original!sum) }
    r := rand();
    sum := sum + r;
  end
  return sum;
}

fun refinement() {
  sum := 0;
  while (sum <= 100) do
    @inv { (= original!sum refinement!sum) }
    @var { (+ 200 refinement!sum) }
    r := randEven();
    sum := sum + r;
  end
  return sum;
}

*/


// this should and does verify
procedure loopRefinement2 () returns (sum: int, sum': int)
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
    // left program. call to randEven 
    havoc r; assume 0 <= r && r < 10 && r mod 2 == 0;
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