interface I =

  class Cell { value: int; rep: rgn; }
  public x: int
  public y: int

end

module Impl : I =

  class Cell { value: int; rep: rgn; }

  meth test1 () : int =
    var x: int in
    havoc x;
    result := x;

end

bimodule ImplREL (Impl | Impl) =

  /* test1 | test1 : true ==e> Agree result */
  meth test1 (|) : (int|int)
    ensures { Agree result }
  = Var x: int | x: int in
    (havoc x | skip);
    HavocR x { Agree x }; /* TODO: Change to "havocRight" */
    |_ result := x _|;

  predicate sameParity(n: int | n: int) =
    [< n mod 2 <] = [> n mod 2 >]

  meth test1_again (|) : (int|int)
    ensures { sameParity(result|result) }
  = Var x: int | x: int in
    ( havoc x | skip );
    HavocR x { sameParity(x|x) };
    |_ result := x _|;

  meth test1_again2 (|) : (unit | unit)
    ensures { Agree x /\ Agree y }
  = ( havoc x; havoc y | skip );
    HavocR y { Agree y };
    HavocR x { Agree x /\ Agree y };

  meth testing (p: Cell | r: rgn) : (unit|Cell)
    requires { exists |q:Cell in r. p =:= q }
    ensures  { [> result in r |> /\ p =:= result }
  = Var | q: Cell in
    HavocR q { [> q in r |> /\ p =:= q };
    (skip | result := q);
end

module A : I =

  class Cell { value: int; rep: rgn; }

  meth test2 (n: int) : int
    effects { rd n }
  = var x: int in
    x := n;
    result := x;

end

module B : I =

  class Cell { value: int; rep: rgn; }

  meth test2 (n: int) : int
    effects { rd n }
  = var x: int in
    var b: int in
    x := 0;
    havoc b;
    while b <> 0 do
      x := x+1;
      havoc b;
    done;
    result := x

end

bimodule AB (A | B) =

  meth test2 (n: int | n: int) : (int | int)
    requires { Both (n >= 0) }
    ensures { Agree result }
    effects { rd n | rd n }
  = Var x: int | x: int in
    Var | b: int in
    ( x := n | x := 0 );
    HavocR b { [> b >] = [< x <] - [> x >] };

    WhileR b <> 0 do
      invariant { [< x <] >= [> x >] }
      invariant { [> b >] = [< x <] - [> x >] }
      /* variant { [> b >] } NOTE: Will be written: variant { b } */
      variant { [> b >] }

      (skip | x := x+1);
      HavocR b { [> b >] = [< x <] - [> x >] }

    done;
    |_ result := x _|;

end


