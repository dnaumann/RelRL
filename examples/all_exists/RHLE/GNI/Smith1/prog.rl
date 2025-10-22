interface I =

  meth prog (secret: int) : int
end

module A : I =
  meth prog (secret: int) : int
/*

post: (= smith!1!ret smith!2!ret);

fun smith(secret) {
  if (secret % 2 == 0) then
    ret := 0;
  else
    ret := 1;
  endif
  return ret;
}

*/
end


/* should not and does not verify  */
bimodule FREL (A | A) =
  meth prog (secret: int| secret: int) : (int |int )
  ensures { result =:= result }
 =

  (if (secret mod 2 = 0) then
    result := 0;
  else
    result := 1;
  end | skip);

  (skip | if (secret mod 2 = 0) then
    result := 0;
  else
    result := 1;
  end);


end
