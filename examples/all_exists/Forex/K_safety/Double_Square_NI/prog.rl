interface I =


  public x: int
  public y: int
  public z: int


  meth prog () : unit
  effects { rw y, x, z }
end

module A : I =
  meth prog () : unit
  = y := 0;
    z := 2 * x;
    while (z > 0) do
      z := z - 1;
      y := y + x;
    done
end

module B : I =
  meth prog () : unit
  = y := 0;
    z := x;
    while (z > 0) do
      z := z - 1;
      y := y + x;
    done;
    y := 2 * y;
end

/* verifies */
bimodule FREL (A | B) =
  meth prog (|) : (unit |unit )
  requires { x =:= x }
  ensures { y =:= y }
    effects { rw y, x, z | rw y, x, z }
 =
   
    |_ y := 0 _|; 

    (z := 2 * x | z := x);

    While (z > 0) | (z > 0)  . [< false <] | [> false |> do
      invariant { y =:= 2 * y }
      invariant { z =:= 2 * z }
      
      |_ z := z - 1 _|;
      |_ y := y + x _|;

      (if ( z > 0) then z := z - 1; y := y + x; end | skip);

   done;

   (skip | y := 2 * y);
   
end
