interface I =

  public low : int
  public high : int
  
  meth prog () : int
    effects { rw low, high}
end

module A : I =
  meth prog () : int
/*
*/
end

module B : I =
  meth prog () : int
/*  =


aspecs:
  flipCoin() {
    pre:  true;
    post: (or (= ret! 0) (= ret! 1));
  }

especs:
  flipCoin() {
    choiceVars: n;
    pre:  (or (= n 0) (= n 1));
    post: (= ret! n);
  }

fun run(high, low) {
  flip := flipCoin();
  if (flip == 0) then
    low := high + low;
  else
    skip;
  endif
  return low;
}

pre:  (= run!1!low run!2!low);
post: (= run!1!low run!2!low);

*/
end

/* should not and does not verify  */
bimodule FREL (A | B) =
  meth prog (|) : (int |int )
  requires { low  =:= low }
  ensures { low =:= low }
  effects {  rw low, high  | rw low, high}
 =
  Var flipcoin_ret: int | flipcoin_ret: int in
  Var | choice_var: int in

  /* left program calls with universal spec */
  (havoc flipcoin_ret | skip ); 
  (assume {0 = flipcoin_ret \/ flipcoin_ret = 1} | skip);

  /* right program calls with existential spec with choicevar instantiated with flipcoin_ret1 */
  HavocR flipcoin_ret {flipcoin_ret =:= flipcoin_ret};
  
  (if (flipcoin_ret = 0) then
    low := high + low;
  else
    skip;
  end | skip); 

  (skip | if (flipcoin_ret = 0) then
    low := high + low;
  else
    skip;
  end);

end
