interface I =
  meth prog (n:int) : int
    effects { rd n }
end

module A : I =
  meth prog (n: int) : int
/*
  =
int l;
int h;
int x;

x = *;
x = if (x <= l) then l else x;

[pre]
l_0 == l_1

[post]
x_0 == x_1
*/
end



bimodule FREL (A | A) =
  meth prog (l: int |  l: int) : (int | int)
  requires { l =:= l }
  ensures { result =:= result }
 =

    Var a: bool | a: bool in

    (havoc result | skip);
    (if (result <= l)
      then
        result := l;
      else
        result := result;
      end | skip);

    HavocR result { result =:= result } ;

    (skip | if (result <= l)
            then
              result := l;
            else
              result := result;
            end);
end
