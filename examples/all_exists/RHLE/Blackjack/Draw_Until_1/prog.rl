interface I =

  public handValue : int
  
  meth prog () : int
    effects { rw handValue}
end

module A : I =
  meth prog () : int
/*

*/
end

module B : I =
  meth prog () : int
/*  =
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
end

/* verifies */
bimodule FREL (A | B) =
  meth prog (|) : (int |int )
  requires { 2 <= handValue /\ handValue <= 20 }
  ensures { handValue = 21 }
  effects { rw handValue | rw , f3_h, f4_h}
 =
   requires 2 <= handValue && handValue <= 20;
  ensures handValue == 21;
  modifies handValue;

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


  Var i : int | i: int in
  Var n : int | n: int in
  Var sum: int | sum: int in
  Var flag: int | flag: int in
  Var x: int | x: int in

  |_ i := 1 _|;
  |_ n := 0 _|;
  |_ sum := 0 _|; 

  While (i <= 100) | (i <= 100) .  <| false <] | [> false |> do 
    invariant { f1_l =:= f1_l /\ f2_l =:= f2_l}
    invariant { i =:= i }
  
      |_ flag := f1_l _|; 

      |_ f2_l := flag _|; 

      |_ x := f3_h _|; 


      ( if ((flag <> 0)) then
      n := n + 1;
      sum := sum + x;
    end | skip );

     (skip | if ((flag <> 0)) then
      n := n + 1;
      sum := sum + x;
    end );
      
      |_ i := i + 1 _|; 
  done;

    |_ f4_h := n + sum +  (sum / n) _|; 

end
