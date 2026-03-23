/* https://github.com/hiroshi-unno/coar/blob/299e979bfce7d9b0532586bfc42b449fd0451531/benchmarks/pfwnCSP/cav2021rel/TI_GNI_hFF.clp 

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

specialized with !high1 and !high2

*/


interface I =
  meth prog (low:int) : int
end

module A : I =
  meth prog (low: int) : int

end




bimodule FREL (A | A) =
  meth prog (low: int |  low: int) : (int | int)
  requires { low =:= low }
  ensures { result =:= result }
 =

  Var b: bool | b: bool in
  Var x: int | x: int in

  |_ x := low _|; 

  (havoc b | skip);

  HavocR b { b =:= b };

  While (b) | (b) . <| false <] | [> false |> do
      invariant { x =:= x }
  
      |_ x := x + 1_|; 

      (havoc b | skip);

      HavocR b { b =:= b };
  done;

  |_ result := x _|;
end
