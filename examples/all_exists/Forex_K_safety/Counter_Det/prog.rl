interface I =


  public c: int
  public x: int
  public n: int


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
   
    |_ c := 0 _|; 

    While (x < n) | (x < n)  . <| false <] | [> false |> do
      invariant { c =:= c }
      invariant { x =:= x }

      |_ x := x + 1 _|;
      |_ c := c + 1 _|;
   done;
   
end
