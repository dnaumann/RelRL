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

  meth test1 (|) : (int|int)
    ensures { Agree result }
  = Var x: int | x: int in
    (havoc x | skip);
    HavocR x { Agree x }; 
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
