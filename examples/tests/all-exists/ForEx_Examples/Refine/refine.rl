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
    var temp1 : int in

    result := new Cell; 
    k := time; 

    havoc b;
    if (b)
    then
        result.c := 0;
        result.x := 0;
        while (k > 0)
        do
            k := k - 1;
            temp1 := result.x;
            result.x := temp1 + 1;
        done;
    else
        result.x := 0;
        result.c := 1;
        
        while (k > 0) 
        do
            k := k - 1;
            havoc s0;
            temp1 := result.x;
            result.x := temp1 + s0;
        done;
    end; */
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

    |_ result := new Cell _|;   
    
    |_ k := time _|;

    (havoc b | skip);
    
    (if (b)
    then
        (result.x := 0 );
        (result.c := 0 );
        while (k > 0) do
         effects { rw {result}`any  }
        invariant {let v = result.x in v + k = time } 
        invariant {time <= 0 -> result.x = 0}
        invariant {time > 0 -> k >= 0 }
          k := k - 1;
          temp1 := result.x;
          result.x := (temp1 + 1);
        done;
    else
        result.x := 0;
        result.c := 1;
        while (k > 0) do
             effects { rw {result}`any  }
        invariant {time <= 0 -> result.x = 0}
        invariant {time >= k }
            k := k - 1;
            havoc s0 ;
            temp1 := result.x;
            result.x := (temp1 + s0);
        done;
    end | skip);

    HavocR b { ~ (b =:= b) };
    
    If4 (false) | (b) 
    thenThen
        (skip | result.x := 0);
        (skip | result.c := 0);
        
        WhileR (k > 0) do variant { [> k >]}
          effects { | rw {result}`any }
          (skip | k := k - 1);
          (skip | temp1 := result.x);
          (skip | result.x := (temp1 + 1));
        done;
    thenElse
(skip | result.x := 0);
        (skip | result.c := 1);

        WhileR (k > 0) do  variant { [> k >]}
             effects { | rw {result}`any }
        invariant { [> let v = result.x in v + k = time |> }
        invariant { [> time <= 0 -> result.x = 0 |> } 
        invariant { [> time > 0 -> k >= 0 |> }
          (skip | k := k - 1);
            
          HavocR s0 { [> s0 = 1 |>};
          (skip | temp1 := result.x);
          (skip | result.x := (temp1 + s0));
        done;
    elseThen
        (skip | result.x := 0);
        (skip | result.c := 0);
        
        WhileR (k > 0) do variant { [> k >]}
             effects { | rw {result}`any }
          (skip | k := k - 1);
          (skip | temp1 := result.x);
          (skip | result.x := (temp1 + 1));
        done;
    elseElse
        (skip | result.x := 0);
        (skip | result.c := 1);

        WhileR (k > 0) do variant { [> k >]}
             effects { | rw {result}`any }
        invariant { [> let v = result.x in v + k = time |> }
        invariant { [> time <= 0 -> result.x = 0 |> } 
        invariant { [> time > 0 -> k >= 0 |> }
          (skip | k := k - 1);
            
          HavocR s0 { [> s0 = 1 |>};
          (skip | temp1 := result.x);
          (skip | result.x := (temp1 + s0));
        done;
    end;
end


