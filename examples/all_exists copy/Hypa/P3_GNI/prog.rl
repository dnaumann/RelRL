interface I =
  meth p3_gni () : int
end

module A : I =
  meth p3_gni () : int
  =
    var x: bool in

    havoc x;
    if (x) then
        result := 1;
    else
        result := 2;
    end;
end

bimodule FREL (A | A) =
  meth p3_gni (|) : (int | int)
    ensures  { result =:= result }                 
  = 
    Var x: bool | x: bool in

    (havoc x | skip);

    (if (x) then result := 1 else result := 2 end | skip);

    HavocR x { x =:=  x};
    
    (skip | if (x) then result := 1 else result := 2 end);
end
