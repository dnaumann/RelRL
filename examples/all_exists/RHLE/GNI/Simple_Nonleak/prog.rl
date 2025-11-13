interface I =

  public low : int
  public high : int
  
  meth prog () : int
    effects { rw low, high}
end

module A : I =
  meth prog () : int
/*

pre:  (= nonleak!1!low  nonleak!2!low);
post: (and
        (= nonleak!1!low nonleak!2!low)
        (= nonleak!1!ret nonleak!2!ret));

fun nonleak(high, low) {
  x   := low + high;
  ret := x - high;
  return ret;
}

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
    Var x : int | x: int in

    |_ x := low + high _|;

  |_ result := x - high _|;

end
