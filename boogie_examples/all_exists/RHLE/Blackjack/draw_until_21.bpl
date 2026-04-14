/*

https://github.com/rcdickerson/rhle-benchmarks/blob/main/blackjack/draw-until-21.imp

*/
// Unary existential spec. 

var handValue: int;

// verifies
procedure biprog () returns ()
  requires 2 <= handValue && handValue <= 20;
  ensures handValue == 21;
  modifies handValue;
{  
  var draw_ret: int;
  var choice_var: int;
  
  while (handValue < 21)
    invariant handValue <= 21;
  {
    assume 1 <= choice_var && choice_var <= 10;
    assume ((handValue + choice_var) <= 21 );
    assert (exists v: int :: v == choice_var);
    havoc draw_ret; assume draw_ret == choice_var;  // models existential call to draw.

    
    handValue := handValue + draw_ret;

  }

}