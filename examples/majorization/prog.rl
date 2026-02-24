interface I =
  meth m (x:int) : int
    requires { x >= 4 }
    ensures  { result > 0 }
    effects  { rd x }
end

module P0 : I =
  meth m (x:int) : int =
    var y : int in
    var z : int in
    var w : int in
    y := x;
    z := 24;
    w := 0;
    while (y > 4) do
      invariant { z > 0 /\ y >= 4 }
      if (w mod 2 = 0) then
         z := z * y;
         y := y - 1;
      end;
      w := w + 1;
    done;
    result := z;
end

module P1 : I =
  meth m (x:int) : int =
    var y : int in
    var z : int in
    var w : int in
    y := x;
    z := 16;
    w := 0;
    while (y > 4) do
      invariant { z > 0 /\ y >= 4 }
      if (w mod 3 = 0) then
         z := z * 2;
         y := y - 1;
      end;
      w := w + 1
    done;
    result := z;
end

bimodule PREL (P0 | P1) =

  meth m (x:int | x:int) : (int|int)
    requires { x =:= x }
    requires { Both (x >= 4) }
    ensures { [< result <] > [> result >] }
  = Var y : int | y : int in
    Var z : int | z : int in
    Var w : int | w : int in
    |_ y := x _|;
    ( z := 24 | z := 16 );
    |_ w := 0 _|;
    While (y > 4) | (y > 4) .
      <| (w mod 2) <> 0 <] | [> (w mod 3) <> 0 |> do
      invariant { y =:= y }
      invariant { Both (y >= 4) }
      invariant { [> z >] > [0] /\ [< z <] > [> z >] }
      If (w mod 2 = 0) | (w mod 3 = 0) then
         ( z := z * y | z := z * 2 );
         |_ y := y - 1 _|;
      end;
      |_ w := w + 1 _|;
    done;
    |_ result := z _|;

end
