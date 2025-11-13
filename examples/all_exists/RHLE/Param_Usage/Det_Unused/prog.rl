interface I =

  public handValue : int
  
  meth prog () : int
    effects { rw handValue}
end

module A : I =
  meth prog () : int
/*

expected: valid;

forall: unused[1];
exists: unused[2];

pre:  (not (= unused!1!param unused!2!param));
post: (= unused!1!ret   unused!2!ret);

fun unused(param) {
  ret := 5;
  return ret;
}

*/
end

/* verifies */
bimodule FREL (A | A) =
  meth prog (param :int | param: int) : (int | int)
  requires { [< param <] <> [> param >] }
  ensures { result =:= result }
 =
    |_ result := 5_|; 
end
