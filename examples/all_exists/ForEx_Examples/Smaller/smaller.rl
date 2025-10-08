interface I =
  meth smaller (time: int) : int
    effects { rd time }
end

module A : I =
  meth smaller (time: int) : int
  =
    var k: int in 
    var b: bool in

    k := time;
    result := 0;

    while (k > 0) do
        k := k - 1;
        
        havoc b;

        if (b) then
            result := result + 1;
        else
            result := result + 3;
        end;
    done;
end

module B : I =
  meth smaller (time: int) : int
  =
    var k: int in 
    var b: bool in

    k := time;
    result := 0;

    while (k > 0) do
        k := k - 1;
        
        havoc b;

        if (b) then
            result := result + 1;
        else
            result := result + 3;
        end;
    done;
end

bimodule FREL (A | B) =
  meth smaller (time : int | time : int) : (int | int)
    requires { time =:= time }
    ensures  { [> result >] <= [< result <]  }                 
  = 
    Var k: int | k: int in
    Var b: bool | b: bool in

    |_ k := time _|;

    |_ result := 0 _|; 

    While (k > 0) | (k > 0) .  [> false |> | [> false |> do
     invariant { [> result >] <= [< result <] }
    
        |_ k := k - 1 _|;
        
        (havoc b | skip);

        If (b) | false then
            (result := result + 1 | skip);
        else
            (result := result + 3 | skip);
        end;

        HavocR b { b =:= b };

        If false | (b) then
            (skip | result := result + 1 );
        else
            (skip | result := result + 3);
        end;

    done;
end
