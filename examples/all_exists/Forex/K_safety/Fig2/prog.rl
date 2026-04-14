interface I =


  public x: int
  public y: int


  meth prog () : unit
  effects { rw y, x } 


end

module A : I =
  meth prog () : unit
  =
  x := 1;
  y := 2 * x;

  while (y > 0) do
      y := y - 1;
      x := 2 * x;
  done;


end

module B : I =
  meth prog () : unit
  = 
  x := 1;
  y :=  x;

  while (y > 0) do
      y := y - 1;
      x := 4 * x;
  done;
end

/* verifies */
bimodule FREL (A | B) =
  meth prog (|) : (unit |unit )
  requires { (x =:= x) }
  ensures { (x =:= x) }
    effects { rw y, x | rw y, x }
 =
   
    |_ x := 1 _|; 

    (y := 2 * x | y := x);

    While (y > 0) | (y > 0)  . <| false <] | [> false |> do
      invariant { x =:= x }
      invariant { y =:= 2 * y }
      
      |_ y := y - 1 _|;
      ( x := 2 * x | x := 4 * x);

      (if (y > 0) then y := y - 1; x := 2 * x; end | skip);
              

   done;
   
end
