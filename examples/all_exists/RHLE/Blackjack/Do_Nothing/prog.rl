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
  return handValue;
}

*/
end

/* should not and does not verify */
bimodule FREL (A | B) =
  meth prog (|) : (int |int )
  requires { 2 <= handValue /\ handValue <= 20 }
  ensures { handValue = 21 }
  effects { rw handValue | rw , f3_h, f4_h}
 =

end
