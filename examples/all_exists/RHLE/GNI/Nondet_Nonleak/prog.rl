interface I =

  public low : int
  public high : int
  
  meth prog () : int
    effects { rw low, high}
end

module A : I =
  meth prog () : int
/*

aspecs:
  randInt() {
    pre: true;
    post: (and (>= ret! 0) (< ret! 100));
  }

especs:
  randInt() {
    choiceVars: n;
    pre: (and (>= n 0) (< n 100));
    post: (= ret! n);
  }

fun nonleak(high, low) {
  r := randInt();
  if (r == 5000) then
    ret := high + low;
  else
    ret := low;
  endif
  return ret;
}


pre: (= nonleak!1!low nonleak!2!low);
post: (and
        (= nonleak!1!low nonleak!2!low)
        (= nonleak!1!ret nonleak!2!ret));

*/
end

/* verifies  */
bimodule FREL (A | A) =
  meth prog (|) : (int |int )
  requires { low  =:= low }
  ensures { low =:= low }
  ensures { result =:= result }
  effects {  rw low, high  | rw low, high}
 =
  Var randint_ret : int | randint_ret : int in

  /* left program calls with universal spec */
  ( havoc randint_ret | skip);
  (assume { 0 <= randint_ret /\ randint_ret < 100 } | skip);

  /* right program calls with existential spec with choicevar instantiated with randint_ret1 */
  HavocR randint_ret { randint_ret =:= randint_ret };
  
  (if (randint_ret = 5000) then
    result := high + low;
  else
    result := low;
  end | skip);

  (skip | if (randint_ret = 5000) then
    result := high + low;
  else
    result := low;
  end);

end
