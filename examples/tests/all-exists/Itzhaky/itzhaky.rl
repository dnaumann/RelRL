interface I =
  
  class Cell {sum: int; b: int; }
  
  meth itzhaky (a: int array, n: int) : Cell
    effects { rd a; rd n; rw alloc }
end

module A : I =

  class Cell {sum: int; b: int; }

  meth itzhaky (a: int array, n: int) : Cell
 
end

bimodule FREL (A | A) =
  meth itzhaky  (a: int array, n: int | a: int array, n: int) : (Cell | Cell)
    requires { a =:= a /\ n =:= n }
    ensures  {[> let x = result.b in x <  0 |> /\ let sum | sum = result.sum | result.sum in sum =:= sum}            
  = 
    Var i: int | i: int in
    Var y: int | y: int in
    Var b: int | b: int in 
    Var sum: int | sum : int in
    Var temp: int | temp: int in

    |_ sum := 0 _|;
    (havoc b | skip);
    HavocR b { <| b < 0 <] };

    If4 (b > 0) | (b > 0) 
    thenThen
      |_ i := 0 _|;

      WhileL (i < n - 1) do variant { [< i <] }
         (temp := get(a, i) | skip);
         (sum := sum + temp | skip);
         (i := i + 1 | skip);
      done;
      WhileR (i < n - 1) do variant { [> i >] }
         (skip | temp := get(a, i));
         (skip | sum := sum + temp);
         (skip | i := i + 1);
      done;
    thenElse
      (i := 0 | i := 1);

      While (i < n - 1) | (i < n)  . <| false <] | [> false |> do
        invariant { <| i < n - 1 <] <-> [> i < n |>} 
        invariant {i + 1 =:= i}
        invariant {sum =:= sum} 
        (temp := get(a, i) | skip);
        (sum := sum + temp | skip);
        (i := i + 1 | skip);
        (skip | temp := get(a, i) );
        HavocR y { [> y >] = [> -temp  - sum >] + [< sum <] };
        (skip | temp := get(a, i) );
        (skip | sum := sum + temp + y);
        (skip | i := i + 1);
      done;
    
    elseThen
      (i := 1 | i := 0);
      WhileL (i < n) do 
        (havoc y | skip);
        (temp := get(a, i) | skip);
        (sum := sum + temp + y | skip);
        (i := i + 1 | skip);
      done;
      WhileR (i < n - 1) do variant { [> i >] }
        (skip | temp := get(a, i));
        (skip | sum := sum + temp);
        (skip | i := i + 1);
      done;
    
    elseElse
      |_ i := 1 _|;

      While (i < n) | (i < n) . <| false <] | [> false |> do
        invariant { <| i < n <] <-> [> i < n |>} 
        invariant {i =:= i}
        invariant {sum =:= sum} 

        (havoc y | skip);
        (temp := get(a, i) | skip);
        (sum := sum + temp + y | skip);

        (i := i + 1 | skip);
          (skip | temp := get(a, i) );
        HavocR y { [> y >] = [> -temp  - sum >] + [< sum <] };
        (skip | temp := get(a, i));
        (skip | sum := sum + temp + y);
        (skip | i := i + 1);
      done;
    end;

    |_ result := new Cell _|;
    |_ result.sum := sum _|;
    |_ result.b := b _|; 
end
