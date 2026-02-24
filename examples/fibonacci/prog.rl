interface FIB =
  meth fib (n: int) : int
    requires { n >= 2 }
    effects { rd n; rw alloc }
end

module Fib1 : FIB =
  class IntArray { length: int; slots: int array; }
  meth fib (n: int) : int
  = var arr: IntArray in
    var sz: int in
    var i: int in
    sz := n+2;
    arr := new IntArray[sz];
    arr[0] := 0;
    arr[1] := 1;
    i := 2;
    while (i <= n) do
      invariant { 2 <= i /\ i <= n+1 }
      effects { rw {arr}`slots }
      var m1: int in
      var m2: int in
      m1 := arr[i-1];
      m2 := arr[i-2];
      arr[i] := m1+m2;
      i := i+1;
    done;
    result := arr[n];
end

module Fib2 : FIB =
  import theory Fib_theory
  extern fib_spec (int) : int

  meth fib (n: int) : int
    ensures { result = fib_spec(n) }
  = var a: int in
    var b: int in
    var i: int in
    i := 2;
    a := 0; b := 1;
    while (i <= n) do
      invariant { 2 <= i /\ i <= n+1 }
      invariant { a = fib_spec(i-2) /\ b = fib_spec(i-1) }
      var tmp: int in
      tmp := a+b;
      a := b;
      b := tmp;
      i := i+1;
    done;
    result := b;
end

bimodule FibREL (Fib1 | Fib2) =

  meth fib(n: int | n: int) : (int | int)
    requires { Both (n >= 2) }
    requires { n =:= n }
    ensures  { result =:= result }
    effects  { rd n; rw alloc | rd n; rw alloc }
  = Var | a: int in
    Var | b: int in
    Var arr: IntArray | in 
    Var sz: int | in
    Var i: int | i: int in
    ( sz := n+2 | skip );
    ( arr := new IntArray[sz] | skip );
    ( arr[0] := 0 | skip );
    ( arr[1] := 1 | skip );
    |_ i := 2 _|;
    ( skip | a := 0; b := 1 );
    While (i <= n) | (i <= n) . <| false <] | [> false |> do
      invariant { i =:= i }
      invariant { Both(2 <= i /\ i <= n+1) }
      invariant { let v| = arr[i-2] in v =:= a }
      invariant { let v| = arr[i-1] in v =:= b }
      effects { rw {arr}`slots | }
      ( var m1: int in var m2: int in 
        m1 := arr[i-1]; 
	m2 := arr[i-2]; 
	arr[i] := m1+m2; 
	i := i+1
      | var tmp: int in 
        tmp := a+b; 
	a := b; 
	b := tmp;
	i := i+1 )
    done;
    ( result := arr[n] | result := b );
end
