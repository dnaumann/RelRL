interface I =
  ghost choice_var: int

  meth flipcoin () : int

  meth prog () : int
    effects {  }
end

module A : I =
  meth prog () : int

  meth flipcoin (): int
    ensures {result = 0 \/ result = 1}

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


  meth flipcoin (): int
    requires {choice_var = 0 \/ choice_var = 1}
    ensures {result = choice_var}
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
  meth flipCoin (|) : (int | int)
   requires {[> choice_var = 0 \/ choice_var = 1 |>}
   ensures { <| result = 0 \/ result = 1 <] }
   ensures { [> result = choice_var |>}

  meth prog (|) : (int | int)
  requires {[> choice_var = 0 \/ choice_var = 1 |>}
  ensures { result =:= result }
 =

  Var | choice_var : int in
  Var flipret: int | flipret: int in

  |_ flipret := flipcoin() _|;
  Assume { [< 1 -  flipret <] = [> choice_var >]};

  
  (if (flipret = 0) then
    result := 10;
  else
    result := 20;
  end  | if (flipret = 0) then
      result := 20;
    else
      result := 10;
    end);

end
