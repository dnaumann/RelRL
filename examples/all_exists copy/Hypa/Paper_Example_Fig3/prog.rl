interface I =
  meth paper_example_fig3 (a: int) : int
    effects { rd a }
end

module A : I =
  meth paper_example_fig3 (a: int) : int
  =
    var k: int in
    var x: int in
    var t: bool in

    k := a; 
    
    havoc x;
    havoc t;

    while (t) do
        havoc t;
        x := x + 1;
    done;

    result := x;

    while (result > 0) do
        result := result - 1;
        k := k + x;
    done;
end

module B : I =
  meth paper_example_fig3 (a: int) : int
  =
    var k : int in
    var x : int in

    k := a;

    havoc x;
    result := x;
    while (result > 0) do
        result := result - 1;
        k := k + x;
    done;
end

bimodule FREL (A | B) =
  meth paper_example_fig3 (a : int | a : int) : (int | int)
    requires { a =:= a }
    ensures  { result =:= result }                 
  = 
    Var k: int | k: int in
    Var x: int | x: int in
    Var t: bool | in

    |_ k := a _|;
    
    (havoc x | skip);
    (havoc t | skip);

    (while (t) do
        havoc t;
        x := x + 1;
    done | skip);

    HavocR x { x =:= x };

    |_ result := x _|;

    While (result > 0) | (result > 0) . [> false |> | [> false |> do
      invariant { result =:= result }
        |_ result := result - 1 _|;
        |_ k := k + x _|;
    done;
end
