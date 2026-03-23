/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/blackjack/draw-once.imp

*/

// Unary existential spec. 

var handValue: int;

// should not and does not verify
procedure biprog () returns ()
  requires 2 <= handValue && handValue <= 20;
  ensures handValue == 21;
  modifies handValue;
{  
  var draw_ret: int;
  var choice_var: int;
  
  assume 1 <= choice_var && choice_var <= 10;
  assert ((handValue + choice_var) == 21 );
  havoc draw_ret; assume draw_ret == choice_var;
  assume (draw_ret + (handValue) == 21);

  handValue := handValue + draw_ret;

}