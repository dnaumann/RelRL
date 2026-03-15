/*

// A blackjack strategy that draws until hitting 21 or going bust.
// This strategy does guarantee the possibility of 21 for every
// possible starting hand.

expected: valid;

exists: play;

pre: (and
       (>= play!handValue 2)
       (<= play!handValue 20));
post: (= play!handValue 21);

aspecs:
  draw() {
    post: (and (>= ret! 1) (<= ret! 10));
  }

especs:
  draw() {
    choiceVars: c;
    pre: (and (>= c 1) (<= c 10));
    post: (= ret! c);
  }

fun play() {
  while (handValue < 21) do
    @inv { (<= play!handValue 21) }
    @var { (- 30 play!handValue) }
    card := draw();
    handValue := handValue + card;
  end
  return handValue;
}

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