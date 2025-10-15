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
if (x >= l) {
    skip;
} else {
    while (true) {
        skip;
    }
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
*/
end


bimodule FREL (A | B) =
  meth prog (l: int |  l: int) : (int | int)
  requires { l =:= l }
  ensures { result =:= result }
 =

    Var a: bool | a: bool in

    (havoc result | skip);
    
    (if (result >= l)
    then
        call skip();?
    else
        while (true) do 
           call skip(); procedures?
        done;
    end | skip);
    
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
