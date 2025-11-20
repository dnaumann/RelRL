interface I =
  
  class Cell {sum: int; b: int; }
  
  meth itzhaky (a: int array, n: int) : Cell
    effects { rd a; rd n; rw alloc }
end

module A : I =

  class Cell {sum: int; b: int; }

  meth itzhaky (a: int array, n: int) : Cell
  /*
  Fig 5 in Itzhaky et al

Original code (in boogie syntax)

  sum1 := 0;
  havoc b1;
  if (b1 > 0)
  { i1 := 0;
    while (i1 < n1 - 1)
    { sum1 := sum1 + A1[i1]; i1 := i1 + 1; }
  } else {
    i1 := 1;
    while (i1 < n1)
    { havoc y1; sum1 := sum1 + A1[i1] + y1; i1 := i1 + 1; } 
  }

Their spec is in OHyperLTL and asserts alignment of iterations.
We use postcondition that describes after last iteration, see below.

  */
 
end

bimodule FREL (A | A) =

  meth itzhaky  (a: int array, n: int | a: int array, n: int) : (Cell | Cell)
    requires { a =:= a /\ n =:= n }
    requires { Both (n  < length(a)) }
    ensures  {[> let x = result.b in x <  0 |> /\ let sum | sum = result.sum | result.sum in sum =:= sum}  
    effects {rw alloc | rw alloc}          
  = 
    Var i: int | i: int in
    Var y: int | y: int in
    Var b: int | b: int in 
    Var sum: int | sum : int in
    Var temp: int | temp: int in

    |_ sum := 0 _|;
    (havoc b | skip);
    HavocR b { [> b < 0 |> };

    If4 (b > 0) | (b > 0) 
    thenThen
      |_ i := 0 _|;

      (while (i < n - 1) do variant {  i  }
         temp := get(a, i);
         sum := sum + temp;
         i := i + 1;
      done | skip);
      (skip | while (i < n - 1) do variant { i }
         temp := get(a, i);
         sum := sum + temp;
         i := i + 1;
      done);
    thenElse
      (i := 0 | i := 1);

      While (i < n - 1) | (i < n)  . <| false <] | [> false |> do
        invariant { <| i < n - 1 <] <-> [> i < n |>} 
        invariant {i + 1 =:= i}
        invariant {Both (0 <= i) }
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
      (while (i < n) do 
        invariant { 0 <= i  }
        havoc y;
        temp := get(a, i);
        sum := sum + temp + y;
        i := i + 1;
      done | skip);
      (skip | while (i < n - 1) do variant {  i }
          invariant { (0 <= i) }
        temp := get(a, i);
        sum := sum + temp;
        i := i + 1;
      done );
    
    elseElse
      |_ i := 1 _|;

      While (i < n) | (i < n) . <| false <] | [> false |> do
        invariant { <| i < n <] <-> [> i < n |>} 
        invariant {i =:= i}
        invariant {sum =:= sum} 
        invariant { Both ( 0 <= i ) }

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
