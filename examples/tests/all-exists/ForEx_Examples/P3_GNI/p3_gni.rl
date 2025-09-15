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

module B : I =
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

bimodule FREL (A | B) =
  meth p3_gni (|) : (int | int)
    ensures  { result =:= result }                 
  = 
    Var x: bool | x: bool in

    (havoc x | skip);
    If (x) | (false) then
        (result := 1 | skip);
    else
        (result := 2 | skip);
    end;

    HavocR x { x =:=  x};
    
    If (false) | (x) then
        (skip | result := 1);
    else
        (skip | result := 2);
    end;
end
