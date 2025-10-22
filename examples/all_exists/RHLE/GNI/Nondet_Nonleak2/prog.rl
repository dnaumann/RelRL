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

pre:  (= run!1!low run!2!low);
post: (= run!1!low run!2!low);

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
  if (low < high) then
    low := 0;
  else
    low := 1;
  endif

  flip := flipCoin();
  if (flip == 0) then
    low := 1 - low;  // Flip low.
  endif
  return low;
}


*/
end

/*  should not and does not verify  */
bimodule FREL (A | B) =
  meth prog (|) : (int |int )
  requires { low  =:= low }
  ensures { low =:= low }
  effects {  rw low, high  | rw low, high}
 =
  Var flipcoin_ret: int | flipcoin_ret: int in
  Var | choice_var: int in 
  
  (if (low < high) then
    low := 0;
  else
    low := 1;
  end | skip);

  (skip | if (low < high) then
    low := 0;
  else
    low := 1;
  end);
  
  /* left program calls with universal spec */
  (havoc flipcoin_ret | skip); 
  (assume {0 = flipcoin_ret \/ flipcoin_ret = 1} | skip );


  /* right program calls with existential spec with choicevar */
  /* syntax error at line 84 col 74.
  HavocR flipcoin_ret {(low =:= low -> flipcoin_ret =:= flipcoin_ret) /\
                       ([< low <]  <> [> low >] -> ([> flipcoin_ret >] = ([< 1 - flipcoin_ret <]) ))};
  

  (if (flipcoin_ret = 0) 
  then
    low := 1 - low; 
  end | skip );
  
  (skip | if (flipcoin_ret = 0) 
  then
    low := 1 - low; 
  end );
  
end
