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
bool a;

x = l;
a = *;
while(a) {
    x = x + 1;
    a = *;
}

*/
end

module B : I =
  meth prog (n: int) : int
/*  =
int l;
int h;
int x;

x = *;
if (x >= l) {
    skip;
} else {
    while (true) {
        skip;
    }
}

[pre]
l_0 == l_1

[post]
x_0 == x_1
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

    (skip | if (result >= l)
            then
              call skip();?
            else
        while (true) do 
           call skip(); procedures?
        done;
            end);


    

end
