/*

// A nonrefinement involving a simple loop.

expected: invalid;

forall: refinement;
exists: original;

post: (= original!sum refinement!sum);

aspecs:
  biggerRand() {
    post: (and (<= 0 ret!) (< ret! 11));
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
    r := rand();
    sum := sum + r;
  end
  return sum;
}

fun refinement() {
  sum := 0;
  while (sum <= 100) do
    @inv { (= original!sum refinement!sum) }
    r := biggerRand();
    sum := sum + r;
  end
  return sum;
}

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
