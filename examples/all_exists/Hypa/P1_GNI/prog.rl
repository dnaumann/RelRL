interface I =
  meth prog () : int
end

module A : I =
  meth prog () : int
/*
int h;
int o;

if (h > 0) {
    o = - o;
} else {
    o = -o + (h - h);
}
*/
end

bimodule FREL (A | A) =
  meth prog (o: int| o: int) : (int | int)
    requires { o =:= o }
    ensures  { result =:= result }                 
  = 

    Var h: int | h: int in


    (havoc h | skip);

    (if (h > 0 ) then
        o := -o;  
    else
        o := -o + (h - h) 
    end| skip); 

    HavocR h { h =:= h };
    
    (skip | if (h > 0)
          then
              o := -o;        
          else
              o := -o + (h - h);
          end);
    
    |_ result := o _|;
end
