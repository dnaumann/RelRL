interface I =
  meth fact (n:int) : int
    requires { n >= 0 }
    ensures { result > 0 }
    effects { rd n }
end

module M0 : I =
  meth fact (n:int) : int =
    var i: int in
    i := 0;
    result := 1;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { result > 0 }
      i := i+1;
      result := result*i;
    done;
end

module M1 : I =
  meth fact (n:int) : int =
    var i: int in
    i := 1;
    result := 1;
    while (i <= n) do
      invariant { 1 <= i /\ i <= n+1 }
      invariant { result > 0 }
      result := result*i;
      i := i+1;
    done;
end

bimodule MREL (M0 | M1) =
  meth fact (n:int|n:int) : (int|int)
    requires { Both (n >= 0) }
    requires { n =:= n }
    ensures { Both (result > 0) }
    ensures { result =:= result }
  = Var i:int | i:int in
    ( i := 0 | i := 1 );
    |_ result := 1 _|;
    While (i < n) | (i <= n) . <| false <] | [> false |> do
      invariant { i+1 =:= i }
      invariant { result =:= result }
      invariant { <| 0 <= i /\ i <= n <] }
      invariant { [> 1 <= i /\ i <= n+1 |> }
      invariant { Both (result > 0) }
      (i := i+1; result := result*i
      |result := result*i; i := i+1);
    done;
end
