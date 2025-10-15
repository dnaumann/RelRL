interface I =
  meth prog () : int
end

module A : I =
  meth prog () : int
/*
int h;
int o;
int l;
int b;

if (h > 0) {
    o = l + b;
} else {
    o = l + b;
}

*/
end

bimodule FREL (A | A) =
  meth prog (l: int, b: int| l: int, b: int) : (int | int)
    requires { l =:= l }
    requires { b =:= b }
    ensures  { result =:= result }                 
  = 

    Var h: int | h: int in


    (havoc h | skip);

    (if (h > 0 ) then
        result := l + b;  
    else
        result := l + b;  
    end| skip); 

    HavocR h { h =:= h };
    
    (skip | if (h > 0)
          then
            result := l + b;  
          else
            result := l + b;  
          end);
    

end
