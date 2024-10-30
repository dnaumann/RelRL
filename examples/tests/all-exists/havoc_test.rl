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

interface EMPTY =
end

module U : EMPTY =
  /* Example from Unno'21: Constraint-based relational verification */
  meth noninterference (high: int, low: int) : int
    effects { rd high, low }
  = var x: int in
    var b: int in
    if high <> 0 then
      havoc x;
      if x >= low then
        skip
      else
        while true do skip done;
      end;
    else
      x := low;
      havoc b;
      while b <> 0 do
        x := x+1;
        havoc b;
      done;
    end;
    result := x;
end

bimodule UREL (U | U) =

  meth noninterference (high: int, low: int | high: int, low: int) : (int | int)
    requires { Agree low }
    ensures  { Agree result }
    effects  { rd high, low | rd high, low }
  = Var x: int | x: int in
    Var b: int | b: int in

    If4 high <> 0 | high <> 0
    thenThen
      ( havoc x | skip ); HavocR x { Agree x };
      If (x >= low) | (x >= low) then
        |_ skip _|
      else
        ( while true do skip done | skip );
        Assert { Both false };
        ( skip | while true do variant { 0 } skip done );
      end;

    thenElse
      ( havoc x | skip );
      ( if x >= low then skip else while true do skip done end;
      | skip );
      Assert { <| x >= low <] };
      ( skip | x := low );
      HavocR b { [> b >] = [< x <] - [> x >] };
      WhileR b <> 0 do
        invariant { [> b >= 0 |> }
        invariant { [< x <] >= [> x >] }
        invariant { [> b >] = [< x <] - [> x >] }
        variant { [> b >] }
        ( skip | x := x+1 );
        HavocR b { [> b >] = [< x <] - [> x >] }
      done;

    elseThen
      ( x := low; havoc b | skip );
      WhileL b <> 0 do
        invariant { <| x >= low <] }
        ( x := x+1; havoc b | skip );
      done;
      HavocR x { Agree x };
      ( skip
      | if x >= low then skip
        else assert { false }; while true do variant { 0 } skip done
        end; )

    elseElse
      |_ x := low _|;
      ( havoc b | skip ); HavocR b { Agree b };
      While b <> 0 | b <> 0 . do
        invariant { Agree b /\ Agree x }
        |_ x := x+1 _|;
        ( havoc b | skip ); HavocR b { Agree b };
      done;
    end;

    |_ result := x _|;

end



module E : EMPTY =
  /* Example from Beutner'24: Automated software verification of hyperliveness */
  meth noninterference2 (h: int, l: int) : int
    effects { rd h, l }
  = var o: int in
    var x: int in
    if h > l then
      havoc x;
      o := l + x
    else
      havoc x; /* x := any nat */
      if (x > l) then
        o := x;
      else
        o := l
      end;
    end;
    result := o;

end

/* FIXME: Does not verify */
bimodule EREL (E | E) =

  meth noninterference2 (h: int, l: int | h: int, l: int) : (int | int)
    requires { Agree l }
    ensures { Agree result }
    effects { rd h, l | rd h, l }
  = Var o: int | o: int in
    Var x: int | x: int in

    If4 (h > l) | (h > l)

    thenThen
      ( havoc x | skip ); HavocR x { Agree x }; |_ o := l + x _|;

    thenElse

      ( havoc x; o := l+x
      | havoc x;
        if (x > l) then o := x else o := l end );

    elseThen
      ( havoc x;
        if (x > l) then o := x else o := l end
      | skip );
      HavocR x { Agree x };
      ( skip | o := l + x );

    elseElse
      ( havoc x;
        if (x > l) then o := x else o := l end
      | havoc x;
        if (x > l) then o := x else o := l end );
    end;
    |_ result := o _|;

end
