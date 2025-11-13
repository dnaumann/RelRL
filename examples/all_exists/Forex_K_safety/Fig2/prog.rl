interface I =


  public x: int
  public y: int
  public z: int


  meth prog () : unit
  effects { rw c, x }
end

module A : I =
  meth prog () : unit

end

module B : I =
  meth prog () : unit

end

/* verifies */
bimodule FREL (A | B) =
  meth prog (|) : (unit |unit )
  requires {(n =:= n) /\
            (x =:= x)}
  ensures { c =:= c }
    effects { rw c, x | rw c, x }
 =
   
    |_ y := 0 _|; 

    (z := 2 * x | z := x);

    While (z > 0) | (z > 0)  . <| false <] | [> false |> do
      invariant { y =:= 2 * y }
      invariant { z =:= 2 * z }
      
      |_ z := z + 1 _|;
      |_ y := y + x _|;

      (skip | if (z > 0) then
              

   done;
   
end
