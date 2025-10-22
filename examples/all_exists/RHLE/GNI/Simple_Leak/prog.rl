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

pre:  (= leak!1!low  leak!2!low);
post: (and
        (= leak!1!low leak!2!low)
        (= leak!1!ret leak!2!ret));

fun leak(high, low) {
  ret := high + low;
  return ret;
}

*/
end

/* should not and does not verify  */
bimodule FREL (A | B) =
  meth prog (|) : (int |int )
  requires { low  =:= low }
  ensures { low =:= low }
  ensures { result =:= result }
  effects {  rw low, high  | rw low, high}
 =
  |_ result := high + low _|;

end
