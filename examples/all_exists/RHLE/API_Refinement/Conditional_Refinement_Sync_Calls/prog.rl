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
    ret := 20; |_ flipret := flipcoin() _|;
  endif
  return ret;
}

  pre:  true;
  post: (= original!ret refinement!ret);
*/
end

/* verifies */
bimodule FREL (A | B) =
  meth flipcoin (|) : (bool | bool)
   ensures { [< not result <] = [> result >]}
  = 
    (havoc result | skip);
    HavocR result { not result =:= result };


  meth prog (|) : (int | int)
  ensures { result =:= result }
 =

  Var flipret: bool | flipret: bool in

  
  |_ flipret := flipcoin() _|;
  
  (if (flipret) then
    result := 10;
  else
    result := 20;
  end  | if (flipret) then
      result := 20;
    else
      result := 10;
    end);

end
