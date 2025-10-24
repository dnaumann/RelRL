interface I =
  meth prog (n:int) : int
    effects { rd n }
end

module A : I =
  meth prog (n: int) : int
/*

*/
end

module B : I =
  meth prog (n: int) : int
/*  =

*/
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
