interface REFINE =

  class Cell {c: int; x: int; }

  meth refine (time: int) : Cell
   effects {rd time; rw alloc}
end

module A : REFINE =

  class Cell {c: int; x: int; }

  meth refine (time: int): Cell
  /* =
    var k: int in
    var s0: int in
    var b: bool in

    var c: int in
    var x: int in
    
    k := time; 

    havoc b;
    if (b)
    then
        x := 0;
        c := 0;
        
        while (k > 0)
        do
            k := k - 1;
            x := x + 1;
        done;
    else
        x := 0;
        c := 1;
        
        while (k > 0) 
        do
            k := k - 1;
            havoc s0;
            x := x + s0;
        done;
    end; 

    result := new Cell;
    result.c = c;
    result.x = x;
*/

end


bimodule Birefine ( A | A ) =

  meth refine (time: int | time: int) : (Cell | Cell)
    requires { time =:= time }
    ensures { <| result.c = 0 <] ->  ([> result.c = 1 |> /\ let x|x = result.x | result.x in x =:= x) }
    effects { rw alloc | rw alloc }
    =
    Var k: int | k: int in
    Var s0: int | s0: int in
    Var b: bool | b: bool in
    Var temp1: int | temp1: int in
    Var x: int | x: int in
    Var c: int | c: int in
    
    |_ k := time _|;

    (havoc b | skip);
    
    (if (b)
    then
        (x := 0 );
        (c := 0 );
        while (k > 0) do
        invariant {x + k = time } 
        invariant {time <= 0 -> x = 0}
        invariant {time > 0 -> k >= 0 }
          k := k - 1;
          x := (x + 1);
        done;
    else
        x := 0;
        c := 1;
        while (k > 0) do
        invariant {time <= 0 -> x = 0}
        invariant {time >= k }
            k := k - 1;
            havoc s0 ;
            x := (x + s0);
        done;
    end | skip);

    HavocR b { ~ (b =:= b) };
    
    If4 (false) | (b) 
    thenThen
        (skip | x := 0);
        (skip | c := 0);
        
        WhileR (k > 0) do variant { [> k >]}
          (skip | k := k - 1);
          (skip | x := (x + 1));
        done;
    thenElse
        (skip | x := 0);
        (skip | c := 1);

        WhileR (k > 0) do  variant { [> k >]}
        invariant { [> x + k = time |> }
        invariant { [> time <= 0 -> x = 0 |> } 
        invariant { [> time > 0 -> k >= 0 |> }
          (skip | k := k - 1);
            
          HavocR s0 { [> s0 = 1 |>};
          (skip | x := (x + s0));
        done;
    elseThen
        (skip | x := 0);
        (skip | c := 0);
        
        WhileR (k > 0) do variant { [> k >]}
          (skip | k := k - 1);
          (skip | x := (x + 1));
        done;
    elseElse
        (skip | x := 0);
        (skip | c := 1);

        WhileR (k > 0) do variant { [> k >]}
        invariant { [> x + k = time |> }
        invariant { [> time <= 0 -> x = 0 |> } 
        invariant { [> time > 0 -> k >= 0 |> }
          (skip | k := k - 1);
            
          HavocR s0 { [> s0 = 1 |>};
          (skip | x := (x + s0));
        done;
    end;

    |_ result := new Cell _|;
    |_ result.x := x _|;
    |_ result.c := c _|;

end


