interface I =


  public l: int
  public h: int

  meth prog () : int
    effects { rw l, h}
end

module A : I =
  meth prog () : int
/*

*/
end

module B : I =
  meth prog () : int
/*  =



fun parity() {
  if (h % 2 == 1) then
    l := 1;
    h := 1;
  else
    l := 0;
    h := 0;
  endif
  return 0;
}

pre: (and
        (= parity!1!l parity!2!l)

        // Delimited Release
        (= (mod parity!1!h 2) (mod parity!2!h 2)));

post: (= parity!1!l parity!2!l);
*/
end

/* Verifies */
bimodule FREL (A | B) =
  meth prog (|) : (int |int )
  requires {l =:= l}
  requires { [< h mod 2 <] = [> h mod 2 >] } /* delimited release */
  effects {rw l, h | rw l, h}
  ensures { l =:= l }
 =
  (if ((h mod 2) = 1) then
    l := 1;
    h := 1;
  else
    l := 0;
    h := 0;
  end | skip);

  (skip | if ((h mod 2) = 1) then
    l := 1;
    h := 1;
  else
    l := 0;
    h := 0;
  end);

end
