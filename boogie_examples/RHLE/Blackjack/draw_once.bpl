/*

// A blackjack strategy that always draws once then stays.
// This strategy does not guarantee the possibility of 21
// for every possible starting hand.

expected: invalid;

exists: play;

pre: (and
       (>= play!handValue 2)
       (<= play!handValue 20));
post: (= play!handValue 21);

especs:
  draw() {
    choiceVars: c;
    pre: (and (>= c 1) (<= c 10));
    post: (= ret! c);
  }

fun play() {
  card := draw();
  handValue := handValue + card;
  return handValue;
}

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