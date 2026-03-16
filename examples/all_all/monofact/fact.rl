interface I =
  meth fact(n:int) : int
    requires { n >= 0 }
    effects { rd n }
end

module F : I =
  meth fact (n: int) : int
  = var i: int in
    var r: int in
    i := 0;
    r := 1;
    while (i < n) do
      i := i+1;
      r := r*i;
    done;
    result := r;
end

bimodule FREL (F | F) =
  meth fact (n: int | n: int) : (int | int)
    requires { Both (n >= 0) }
    requires { [< n <] >= [> n >] }
    ensures  { [< result <] >= [> result >] }                 
  = Var i: int | i: int in
    Var r: int | r: int in
    |_ i := 0 _|;
    |_ r := 1 _|;
    While (i < n) | (i < n) . [> i = n |> | [> false |> do
      invariant { Both (0 <= i /\ i <= n) }
      invariant { [< i <] >= [> i >] }
      invariant { [> i < n |> -> i =:= i }
      invariant { [< r <] >= [> r >] /\ Both(r >= 1) }
      |_ i := i+1 _|;
      |_ r := r*i _|;
    done;
    |_ result := r _|;
end
