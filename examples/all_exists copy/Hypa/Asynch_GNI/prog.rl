interface I =
  meth prog (n:int) : int
    effects { rd n }
end

module A : I =
  meth prog (n: int) : int
/*
  =
int o;
int x;
int s;

o = 0;
while (x > 0) {
    x = x - 1;
    s = *;
    o = o + s;
}
*/
end

module B : I =
  meth prog (n: int) : int
/*  =
int o;
int x;
int s;
int t;

o = 0;
while (x > 0) {
    x = x - 1;
    s = *;
    t = o + s;
    o = t;
}
*/
end


bimodule FREL (A | B) =
  meth prog (x: int |  x: int) : (int | int)
  requires { x =:= x }
  ensures { result =:= result }
 =
    Var k: int | k: int in /* using k instead of s to avoid state id clash */
    Var | t: int in


    |_ result := 0 _|; 

    While (x > 0) |  (x > 0) . <| false <] | [> false |> do
      invariant { x =:= x }
      invariant { result =:= result }
  
        |_ x := x - 1 _|;
        
        (havoc k | skip) ;
        
        HavocR k  { k =:= k };

        (result := result + k | skip);

        (skip | t := result + k);
        (skip | result := t);
    done;
end
