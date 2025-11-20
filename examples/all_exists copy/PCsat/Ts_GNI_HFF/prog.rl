interface I =
  meth prog (n:int) : int
    effects { rd n }
end

module A : I =
  meth prog (n: int) : int
/*
int l;
int h;
int x;
bool a;

x = l;
a = *;
while(a) {
    x = x + 1;
    a = *;
}


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

  |_result := l _|; 

  (havoc a | skip);

  HavocR a { a =:= a };

  While (a) | (a) . <| false <] | [> false |> do
      invariant { result =:= result }
  
      |_ result := result + 1_|; 

      (havoc a | skip);

      HavocR a { a =:= a };
  done;
end
