interface I =
  meth prog () : int
    effects {  }
end

module A : I =
  meth prog () : int
/*
aspecs:
  flipCoin() {
    pre: true;
    post: (or (= ret! 0) (= ret! 1));
  }

fun refinement() {
  r := flipCoin();
  if (r == 0) then
    ret := 20;
  else
    ret := 10;
  endif
  return ret;
}
*/
end

module B : I =
  meth prog () : int
/*  =
  especs:
    flipCoin() {
      choiceVars: n;
      pre: (or (= n 0) (= n 1));
      post: (= ret! n);
    }

fun original() {
  r := flipCoin();
  if (r == 0) then
    ret := 10;
  else
    ret := 20;
  endif
  return ret;
}

  pre:  true;
  post: (= original!ret refinement!ret);
*/
end

/* verifies */
bimodule FREL (A | B) =
  meth prog (|) : (int | int)
  ensures { result =:= result }
 =

  Var | choice_var : int in
  Var flipret: int | flipret: int in

  (havoc flipret | skip);

  (assume { flipret = 0 \/ flipret = 1} | skip); /* universal spec */
  
  (if (flipret = 0) then
    result := 10;
  else
    result := 20;
  end | skip);

  /* existential spec instantiated with flipret_ref */
  HavocR flipret {  [< 1 -  flipret <] = [>  flipret >]}; 

  (skip | if (flipret = 0) then
      result := 20;
    else
      result := 10;
    end);

end
