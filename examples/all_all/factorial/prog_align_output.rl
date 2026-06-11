/* left  = M0.fact   right = M1.fact */
bimodule M0_M1_REL (M0 | M1) =

  meth fact (n:int|n:int) : (int|int)
    requires { <| n >= 0 <] }
    requires { [> n >= 0 |> }
    requires { Agree n }
    ensures { <| result > 0 <] }
    ensures { [> result > 0 |> }
    ensures { Agree result }
    effects  { rd n | rd n }
  =
    Var  i: int |  in
    Var  |  i: int in
    (i := 0
    | i := 1);
    (result := 1
    | result := 1);
    While i < n | i <= n . <| False <] | [> False |> do
      invariant {i + 1 =:= i}
      invariant {Both (result > 0)}
      invariant {<| 0 <= i /\ i <= n <]}
      invariant {[> 1 <= i /\ i <= n + 1 |>}
      effects {  |  }
      (i := i + 1;
       result := result * i
      | result := result * i;
        i := i + 1)
    done
  ;

end
