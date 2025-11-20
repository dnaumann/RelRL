interface I =


  public l: int
  public h: int

  meth prog () : int
    effects { rw l, h}
end

module A : I =
  meth prog () : int
/*

fun parity() {
  h := h % 2;
  if (h == 1) then
    l := 1;
    h := 1;
  else
    l := 0;
    h := 0;
  endif
  return 0;
}


pre:  (= parity!1!l parity!2!l);
post: (= parity!1!l parity!2!l);
*/
end

/* should not and does not verify */
bimodule FREL (A | A) =
  meth prog (|) : (int |int )
  requires {l =:= l}
  effects {rw l, h | rw l, h}
  ensures { l =:= l }
 =

  |_ h := h mod 2 _|;

  (if (h = 1) then
    l := 1;
    h := 1;
  else
    l := 0;
    h := 0;
  end | skip);

  (skip | if (h = 1) then
    l := 1;
    h := 1;
  else
    l := 0;
    h := 0;
  end);

end
