/*

https://github.com/rcdickerson/rhle-benchmarks/blob/main/blackjack/do-nothing.imp

*/

// Unary existential spec. can be captured as bicommand with skip on left.

var handValue: int;

// should not and does not verify
procedure biprog () returns ()
  requires 2 <= handValue && handValue <= 20;
  ensures handValue == 21;
  modifies handValue;
{  
  assert true;
}