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

expected: invalid;

forall: used[1];
exists: used[2];

pre:  (not (= used!1!param used!2!param));
post: (= used!1!ret used!2!ret);

fun used(param) {
  ret := param % 2;
  return ret;
}
*/
end

/* should not and does not verify */
bimodule FREL (A | B) =
  meth prog (param :int | param: int) : (int | int)
  requires { [< param <] <> [> param >] }
  ensures { result =:= result }
 =
    |_ result := param mod 2_|; 
end