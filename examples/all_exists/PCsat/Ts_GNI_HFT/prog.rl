/* https://github.com/hiroshi-unno/coar/blob/299e979bfce7d9b0532586bfc42b449fd0451531/benchmarks/pfwnCSP/cav2021rel/TS_GNI_hFT.clp

if (high) {
  x = *; // needs to depend on the return value of the other copy
  if (x >= low) { return x; } else { while (1) { } }
} else {
  x = low;
  while ( * ) { x++; }
  return x;
}

Copy 1 is scheduled demonically
Copy 2 is scheduled angelically

specialized with !high1 and high2

*/


interface I =
  meth prog (low:int) : int
end

module A : I =
  meth prog (low: int) : int

end

module B : I =
  meth prog (low: int) : int

end


bimodule FREL (A | B) =
  meth prog (low: int |  low: int) : (int | int)
  requires { low =:= low }
  ensures { result =:= result }
 =

    Var b: bool |  in
    Var x: int | x: int in

    (x := low | skip);
    
    (havoc b | skip);
    (while (b) do
      invariant { x >= low }
        x := x + 1;
        havoc b;
     done | skip);
    
    HavocR x { x =:= x };

    (skip | if (x >= low)
            then
              x := x;
            else
        while (true) do  variant { 42 }
           skip;
        done;
            end);


    |_ result := x _|;

end
