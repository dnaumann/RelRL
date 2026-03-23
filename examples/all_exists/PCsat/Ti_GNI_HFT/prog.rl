/* https://github.com/hiroshi-unno/coar/blob/299e979bfce7d9b0532586bfc42b449fd0451531/benchmarks/pfwnCSP/cav2021rel/TI_GNI_hFT.clp 

if (high) {
  x = *; // needs to depend on the return value of the other copy
  if (x >= low) { return x; } else { return low; }
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
  meth prog (n:int) : int
    effects { rd n }
end

module A : I =
  meth prog (n: int) : int

end

module B : I =
  meth prog (n: int) : int
end


bimodule FREL (A | B) =
  meth prog (l: int |  l: int) : (int | int)
  requires { l =:= l }
  ensures { result =:= result }
 =

    Var a: bool | a: bool in

    (result := l | skip);

    (havoc a | skip);
    
    (while (a) do
      invariant { result >= l }
        result := result + 1;
        havoc a;
     done | skip);


    HavocR result { result =:= result };

    (skip | if (result <= l)
            then
                result := l;
            else
              result := result
            end);
end
