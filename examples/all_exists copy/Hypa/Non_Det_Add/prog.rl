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

o = 0;
while (x > 0) {
    x = x - 1;
    if * {
        o = o + 1;
    } else {
        o = o + 2;
    }
}
*/
end

module B : I =
  meth prog (n: int) : int
/*  =

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


bimodule FREL (A | B) =
  meth prog (x: int |  x: int) : (int | int)
  requires { x =:= x }
  ensures { result =:= result }
 =

    Var | k: int in /* using k instead of s to avoid state id clash */
    Var b: bool | in

    |_ result := 0 _|;

    While (x > 0) |  (x > 0) . <| false <] | [> false |> do
      invariant { x =:= x }
      invariant { result =:= result }
        |_ x := x - 1 _|;

        (havoc b | skip);

        (if (b) then
          result := result + 1;
        else
            result := result + 2;
        end | skip);

        HavocR k { [> k >] = [< result <] - [> result >] };

        (skip | result := result + k);
    done;
end
