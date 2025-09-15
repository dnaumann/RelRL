interface I =
  meth ForEx(n:int) : int
    effects { rd n }
end

module A : I =
  meth ForEx (n: int) : int
  =
    var x: int in
    var b: bool in

    x := n;
    result := 0; 

    while (x > 0) do
        x := x - 1; 

        havoc b;
        if (b) then
            result := result + 1;
        end;
    done;
end

module B : I =
  meth ForEx (n: int) : int
  =
    var x: int in
    var s0: int in  /* 0 suffix to avoid clash with compiler-gend variable s. */
    
    x := n;
    result := 0; 

    while (x > 0) do
        x := x - 1; 

        havoc s0;
        result := result + s0;
    done;
end

bimodule FREL (A | B) =
  meth ForEx (n: int | n: int) : (int | int)
    requires { n =:= n }
    ensures  { result =:= result }                 
  = 
    Var x: int | x: int in
    Var b: bool | in
    Var | s0: int in

    |_ x := n _|; 
    |_ result := 0 _|; 

    While (x > 0) | (x > 0) . [> false |> | [> false |> do
            invariant { x =:= x }
            invariant { result =:= result }
        
        |_ x := x - 1 _|; 

        (havoc b | skip);
        (if (b) then
            result := result + 1 ;
        end | skip);

        HavocR s0 { [> s0 >] = [< result <] - [> result >]  };

        (skip | result := result + s0);
    done;
end
