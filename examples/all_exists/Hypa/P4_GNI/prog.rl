interface I =
  meth prog () : int
end

module A : I =
  meth prog () : int
/*
int o;
int h;

if (h > 0) {
    if * {
        o = 1;
    } else {
        o = 2;
    }
} else {
    if * {
        o = 2;
    } else {
        o = 1;
    }
}


*/
end

bimodule FREL (A | A) =
  meth prog (|) : (int | int)
    ensures  { result =:= result }                 
  = 

    Var x: bool | x: bool in
    Var h: int | h: int in


    (havoc h | skip);
    
    (if (h > 0 )
    then
        havoc x;
        if (x)
        then
          result := 1;
        else
          result := 2;
        end
    else
        havoc x;
        if (x)
        then
            result := 2;
        else
            result := 1;
        end
    end | skip );

    HavocR h  { h =:= h };
   
    If4 (false) | (h > 0)
    thenThen
        HavocR x { x =:= x };
        (skip | if (x)
          then
            result := 1;
          else
            result := 2;
          end);

    thenElse
        HavocR x { x =:= x };
        (skip | if (x)
                then
                  result := 2;
                else
                  result := 1;
                end);

    elseThen
        HavocR x { x =:= x };
        (skip | if (x)
          then
            result := 1;
          else
            result := 2;
          end);
    elseElse
        HavocR x { x =:= x };
        (skip | if (x)
                then
                  result := 2;
                else
                  result := 1;
                end);
    end;
end
