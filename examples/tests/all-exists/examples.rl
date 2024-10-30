interface I =
  /* dummy */
end

module Impl : I =
  /* dummy */
end

bimodule ConditionalLoopAlignmentExample (Impl | Impl) =

  meth m (x:int, n: int | x:int, n: int) : (int|int)
    requires { Both(n > 0) }
    requires { Both(x >= 0) }
    requires { x =:= x }
    ensures { result =:= result }
  = Var y : int | y : int in
    Var z : int | z : int in
    Var w : int | w : int in
    |_ y := x _|;
    |_ z := 0 _|;
    |_ w := 0 _|;
    While (y > 0) | (y > 0) . <| w <> 0 <] | [> w <> 0 |> do
      invariant { y =:= y }
      invariant { Both (0 <= y /\ y <= x) }
      invariant { Both (0 <= w /\ w < n) }
      invariant { z =:= z }
      variant { [> (n - w) mod n >] }
      If (w = 0) | (w = 0) then
         ( havoc z | skip ); HavocR z { z =:= z };
         |_ y := y - 1 _|;
      end;
      |_ w := (w + 1) mod n _|;
    done;
    |_ result := z _|;
end
