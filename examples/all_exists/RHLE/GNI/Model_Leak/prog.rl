interface I =

  public low : int
  public high : int
  
  meth prog (x_h: int) : int
    effects { rw low, high}
end

module A : I =
  meth prog (x_h: int) : int
/*
aspecs:
  randInt() {
    pre:  true;
    post: (and (>= ret! 0) (< ret! 100));
  }
*/
end

module B : I =
  meth prog (x_h: int) : int
/*  =


especs:
  randInt() {
    choiceVars: n;
    pre:  (and (>= n 0) (< n 100));
    post: (= ret! n);
  }

fun leak(high, low) {
  r := randInt();
  if (r == 50) then
    ret := high + low;
  else
    ret := low;
  endif
  return ret;
}


pre:  (= leak!1!low  leak!2!low);
post: (and
        (= leak!1!low leak!2!low)
        (= leak!1!ret leak!2!ret));


*/
end

/* should not and does not verify  */
bimodule FREL (A | B) =
  meth prog (x_h: int|x_h : int) : (int |int )
  requires { low  =:= low }
  ensures { low =:= low }
  ensures { result =:= result }
  effects {  rw low, high  | rw low, high}
 =
  Var randint_ret : int | randint_ret: int in

  /* left program calls with universal spec */
  (havoc randint_ret | skip); 
  (assume {0 <= randint_ret /\ randint_ret < 100} | skip);

  /* right program calls with existential spec with choicevar instantiated with randint_ret1 */
  HavocR randint_ret { randint_ret =:= randint_ret } ;
  
  (if (randint_ret = 50) then
    result := high + low;
  else
    result := low;
  end | skip);

  (skip |   if (randint_ret = 50) then
    result := high + low;
  else
    result := low;
  end);

end
