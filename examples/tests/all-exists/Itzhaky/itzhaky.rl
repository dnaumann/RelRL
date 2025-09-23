interface I =
  
  class Cell {sum: int; b: int; }
  
  meth itzhaky (a: int array, n: int) : Cell
    effects { rd a; rd n; rw alloc; rw {alloc}`any }
end

module A : I =

  class Cell {sum: int; b: int; }

  meth itzhaky (a: int array, n: int) : Cell
 
end

bimodule FREL (A | A) =
  meth itzhaky  (a: int array, n: int | a: int array, n: int) : (Cell | Cell)
    requires { a =:= a}
    requires { n =:= n }
    ensures  {[> result.b < 0 |>}
    ensures  {let sum | sum = result.sum | result.sum in sum =:= sum}            
  = 
    Var i: int | i: int in
    Var y: int | y: int in
    Var b: int | b: int in 
    Var sum: int | sum : int in

    |_ sum := 0 _|;
    (havoc b | skip);
    havocR b { <| b < 0 <] };

    If4 (b > 0) | (b > 0) 
    thenTHen
      WhileL (i < n - 1) do variant { [< i <] }
         (havoc y | skip);
         (sum := sum + a[i] | skip);
         (i := i + 1 | skip);
      done;
      WhileR (i < n - 1) do variant { [> i >] }
         (skip | havoc y);
         (skip | sum := sum + a[i] | skip);
         (skip | i := i + 1 | skip);
      done;
    thenElse
      |_ i := 0 _|;
      While (i < n - 1) | (i < n)  . <| false <] | [> false |> do
        invariant { <| i < n - 1 <] <-> [> i < n |>} 
        invariant {i + 1 =:= i}
        invariant {sum =:= sum} 

        (sum := sum + a[i] | skip);
        (i := i + 1 | skip)

        HavocR y { [> y |> = [> -a[i]  - sum |> + <| sum <] };
        (skip | sum := sum + a[i] + y);
        (skip | i := i + 1);
      done;
    
    elseThen
      (i := 1 | skip);
      whileL (i < n) do variant { [< i <] }
        (havoc y | skip);
        (sum := sum + a[i] + y | skip);
        (i := i + 1 | skip);
      done;
      (skip | i := 0);
      whileR (i < n - 1) do variant { [> i >] }
        (skip | havoc y);
        (skip | sum := sum + a[i] + y);
        (skip | i := i + 1);
      done;
    
    elseElse
      |_ i := 1 _|;

      While (i < n) | (i < n) . <| false <] | [> false |> do
        invariant { <| i < n <] <-> [> i < n |>} 
        invariant {i =:= i}
        invariant {sum =:= sum} 

        (havoc y | skip);
        (sum := sum + a[i] + y | skip);

        (i := i + 1 | skip);

        HavocR y { [> y |> = [> -a[i]  - sum |> + <| sum <] };
        (skip | sum := sum + a[i] + y);
        (skip | i := i + 1);
      done;
    end;

    |_ result := new Cell _|;
    |_ result.sum := sum _|;
    |_ result.b := b _|; 
end
