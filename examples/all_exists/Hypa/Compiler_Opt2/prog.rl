interface I =
  meth compiler_opt(time:int) : int
    effects { rd time }
end

module A : I =
  meth compiler_opt (time: int) : int
  =
  var x: int in 
  var s0: int in /* to avoid clash with compiler naming of state. */
  var t: int in

  x := time; 
  result := 0; 

  while (x > 0) do
    x := x - 1; 

    havoc t;
    while (t > 0) do
    
        t := t - 1;
        havoc s0;
        result := result + s0;
    done;    
  done;
end

module B : I =
  meth compiler_opt (time: int) : int
  =
  var x: int in 
  var s0: int in /* to avoid clash with compiler naming of state. */

  x := time; 
  result := 0; 

  while (x > 0) do
    x := x - 1; 
    havoc s0;
    result := result + s0;
  done;
end

bimodule FREL (A | B) =
  meth compiler_opt (time: int | time: int) : (int | int)
    requires { time =:= time }
    ensures  { result =:= result }                 
  = 
    Var x: int | x: int in
    Var s0: int | s0: int in
    Var t: int | in 

    |_ x := time _|; 
    |_ result := 0 _|;

    While (x > 0) | (x > 0) . [> false |> | [> false |> do
          invariant { result =:= result }
          invariant { time =:= time }
          invariant { x =:= x }
      |_ x := x - 1 _|;

      (havoc t | skip);
      WhileL (t > 0) do
          (t := t - 1 | skip);
          (havoc s0 | skip);
          (result := result + s0 | skip);
      done;
      
      HavocR s0 { [> s0 >] = [< result <] - [> result >] };
      (skip | result := result + s0);
    done;

end
