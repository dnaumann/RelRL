/* From https://github.com/veracity-lang/veracity/blob/main/benchmarks/manual/ht-fizz-buzz.vcy */

interface A =
  import theory Fizzbuzz_Theory
  extern type int_fun with default = empty_fun
  extern const empty_fun : int_fun
  extern add_mapping(int, int, int_fun) : int_fun
  extern getfnval(int, int_fun) : int

  public hmap : int_fun

  meth fizzbuzz(n: int) : unit
    requires { n > 0 }
    requires { forall i:int. getfnval(i, hmap) = 0 }
    ensures  { forall i:int. 0 <= i /\ i < n -> (i mod 3 = 0 \/ i mod 5 = 0)
               -> getfnval(i, hmap) = 1 }
    effects  { rw hmap; rd n }
end

module Fizzbuzz35 : A =
  meth fizzbuzz(n: int) : unit =
    var i: int in
    var one: int in
    one := 1;
    i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0)
                  -> getfnval(j, hmap) = 0 }
      invariant { forall j:int. 0 <= j /\ j < i
                  -> (j mod 3 = 0 <-> getfnval(j, hmap) = 1) }
      if (i mod 3 = 0) then
        hmap := add_mapping(i, one, hmap);
      end;
      i := i + 1;
    done;
    { forall j:int. 0 <= j /\ j < n /\ j mod 3 = 0
      -> getfnval(j, hmap) = 1 };
    i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { forall j:int. 0 <= j /\ j < n /\ j mod 3 = 0
                  -> getfnval(j, hmap) = 1 }
      invariant { forall j:int. 0 <= j /\ j < i /\ j mod 5 = 0
                  -> getfnval(j, hmap) = 1 }
      invariant { forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0 \/ j mod 5 = 0)
                  -> getfnval(j, hmap) = 0 }
      if (i mod 5 = 0) then
        hmap := add_mapping(i, one, hmap);
      end;
      i := i + 1;
    done;
end

module Fizzbuzz53 : A =
  meth fizzbuzz(n: int) : unit =
    var i: int in
    var one: int in
    one := 1;
    i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { forall j:int. 0 <= j /\ j < n /\ ~(j mod 5 = 0)
                  -> getfnval(j, hmap) = 0 }
      invariant { forall j:int. 0 <= j /\ j < i /\ j mod 5 = 0
                  -> getfnval(j, hmap) = 1 }
      if (i mod 5 = 0) then
        hmap := add_mapping(i, one, hmap);
      end;
      i := i + 1;
    done;
    { forall j:int. 0 <= j /\ j < n /\ j mod 5 = 0
      -> getfnval(j, hmap) = 1 };
    i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { forall j:int. 0 <= j /\ j < n /\ j mod 5 = 0
                  -> getfnval(j, hmap) = 1 }
      invariant { forall j:int. 0 <= j /\ j < i /\ j mod 3 = 0
                  -> getfnval(j, hmap) = 1 }
      invariant { forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0 \/ j mod 5 = 0)
                  -> getfnval(j, hmap) = 0 }
      if (i mod 3 = 0) then
        hmap := add_mapping(i, one, hmap);
      end;
      i := i + 1;
    done;
end

bimodule FizzBuzzCommutes (Fizzbuzz35 | Fizzbuzz53) =
  meth fizzbuzz (n:int | n:int) : (unit | unit)
    requires { n =:= n }
    requires { Both (n > 0) }
    requires { Both (forall i:int. getfnval(i, hmap) = 0) }
    ensures { forall i:int | i:int. Both (0 <= i /\ i < n) -> (i =:= i) -> getfnval(i, hmap) =:= getfnval(i, hmap) }
    effects  { rw hmap | rw hmap }
  = Var i:int | i:int in
    Var one:int | one:int in
    |_ one := 1 _|;

    |_ i := 0 _|;
    /* Loop 1: left marks mod 3, right marks mod 5 */
    While (i < n) | (i < n) . <| false <] | [> false |> do
      invariant { i =:= i }
      invariant { Both (0 <= i /\ i <= n) }
      invariant { <| forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0)
                     -> getfnval(j, hmap) = 0 <] }
      invariant { <| forall j:int. 0 <= j /\ j < i
                     -> (j mod 3 = 0 <-> getfnval(j, hmap) = 1) <] }
      invariant { [> forall j:int. 0 <= j /\ j < n /\ ~(j mod 5 = 0)
                     -> getfnval(j, hmap) = 0 |> }
      invariant { [> forall j:int. 0 <= j /\ j < i /\ j mod 5 = 0
                     -> getfnval(j, hmap) = 1 |> }
      ( if (i mod 3 = 0) then
          hmap := add_mapping(i, one, hmap)
        end
      | if (i mod 5 = 0) then
          hmap := add_mapping(i, one, hmap)
        end );
      |_ i := i + 1 _|;
    done;

    |_ i := 0 _|;
    /* Loop 2: left marks mod 5, right marks mod 3 */
    While (i < n) | (i < n) . <| false <] | [> false |> do
      invariant { i =:= i }
      invariant { Both (0 <= i /\ i <= n) }
      invariant { <| forall j:int. 0 <= j /\ j < n /\ j mod 3 = 0
                     -> getfnval(j, hmap) = 1 <] }
      invariant { <| forall j:int. 0 <= j /\ j < i /\ j mod 5 = 0
                     -> getfnval(j, hmap) = 1 <] }
      invariant { <| forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0 \/ j mod 5 = 0)
                     -> getfnval(j, hmap) = 0 <] }
      invariant { [> forall j:int. 0 <= j /\ j < n /\ j mod 5 = 0
                     -> getfnval(j, hmap) = 1 |> }
      invariant { [> forall j:int. 0 <= j /\ j < i /\ j mod 3 = 0
                     -> getfnval(j, hmap) = 1 |> }
      invariant { [> forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0 \/ j mod 5 = 0)
                     -> getfnval(j, hmap) = 0 |> }
      ( if (i mod 5 = 0) then
          hmap := add_mapping(i, one, hmap)
        end
      | if (i mod 3 = 0) then
          hmap := add_mapping(i, one, hmap)
        end );
      |_ i := i + 1 _|;
    done;
end


bimodule FizzBuzzCommutes_Seq (Fizzbuzz35 | Fizzbuzz53) =
  meth fizzbuzz (n:int | n:int) : (unit | unit)
    requires { n =:= n }
    requires { Both (n > 0) }
    requires { Both (forall i:int. getfnval(i, hmap) = 0) }
    ensures { forall i:int | i:int. Both (0 <= i /\ i < n) -> (i =:= i) -> getfnval(i, hmap) =:= getfnval(i, hmap) }
    effects  { rw hmap | rw hmap }
  = Var i:int | i:int in
    Var one:int | one:int in
    |_ one := 1 _|;
 /* 35 order, on left */
    (i := 0;
     while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0)
                  -> getfnval(j, hmap) = 0 }
      invariant { forall j:int. 0 <= j /\ j < i
                  -> (j mod 3 = 0 <-> getfnval(j, hmap) = 1) }
      if (i mod 3 = 0) then
        hmap := add_mapping(i, one, hmap);
      end;
      i := i + 1;
    done;
    assert { forall j:int. 0 <= j /\ j < n /\ j mod 3 = 0
      -> getfnval(j, hmap) = 1 } | skip);
    (i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { forall j:int. 0 <= j /\ j < n /\ j mod 3 = 0
                  -> getfnval(j, hmap) = 1 }
      invariant { forall j:int. 0 <= j /\ j < i /\ j mod 5 = 0
                  -> getfnval(j, hmap) = 1 }
      invariant { forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0 \/ j mod 5 = 0)
                  -> getfnval(j, hmap) = 0 }
      if (i mod 5 = 0) then
        hmap := add_mapping(i, one, hmap);
      end;
      i := i + 1;
    done;
    | skip );

    Assert { <| forall j:int. 0 <= j /\ j < n /\ j mod 3 = 0
                  -> getfnval(j, hmap) = 1 <] };
    Assert { <| forall j:int. 0 <= j /\ j < i /\ j mod 5 = 0
                  -> getfnval(j, hmap) = 1 <] };
    Assert { <| forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0 \/ j mod 5 = 0)
                  -> getfnval(j, hmap) = 0 <] };

   /* 35 order, on right, preserving left conditions */ 
   (skip | i := 0);
    WhileR (i < n) do
      invariant { [> 0 <= i /\ i <= n |> }
      invariant { [> forall j:int. 0 <= j /\ j < n /\ ~(j mod 5 = 0)
                  -> getfnval(j, hmap) = 0 |> }
      invariant { [> forall j:int. 0 <= j /\ j < i /\ j mod 5 = 0
                  -> getfnval(j, hmap) = 1 |> }
      invariant { <| forall j:int. 0 <= j /\ j < n /\ j mod 3 = 0
                  -> getfnval(j, hmap) = 1 <] }
      invariant { <| forall j:int. 0 <= j /\ j < i /\ j mod 5 = 0
                  -> getfnval(j, hmap) = 1 <] }
      invariant { <| forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0 \/ j mod 5 = 0)
                  -> getfnval(j, hmap) = 0 <] }
      (skip| if (i mod 5 = 0) then
        hmap := add_mapping(i, one, hmap);
      end); 
      (skip| i := i + 1); 
    done;

    Assert { <| forall j:int. 0 <= j /\ j < n /\ j mod 3 = 0
                  -> getfnval(j, hmap) = 1 <] };
    Assert { <| forall j:int. 0 <= j /\ j < i /\ j mod 5 = 0
                  -> getfnval(j, hmap) = 1 <] };
    Assert { <| forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0 \/ j mod 5 = 0)
                  -> getfnval(j, hmap) = 0 <] };

    Assert { [> forall j:int. 0 <= j /\ j < n /\ j mod 5 = 0
                -> getfnval(j, hmap) = 1 |> };

    ( skip | i := 0);
    WhileR (i < n) do
      invariant { [> 0 <= i /\ i <= n |> }
      invariant { [> forall j:int. 0 <= j /\ j < n /\ j mod 5 = 0
                  -> getfnval(j, hmap) = 1 |> }
      invariant { [> forall j:int. 0 <= j /\ j < i /\ j mod 3 = 0
                  -> getfnval(j, hmap) = 1 |> }
      invariant { [> forall j:int. 0 <= j /\ j < n /\ ~(j mod 3 = 0 \/ j mod 5 = 0)
                  -> getfnval(j, hmap) = 0 |> }
      (skip | if (i mod 3 = 0) then
        hmap := add_mapping(i, one, hmap);
      end);
      (skip | i := i + 1);
    done;
end


/* Sum commutativity: summing in order [0,n/2) [n/2,n)
   vs [n/2,n) [0,n/2) yields the same total. */

interface B =
  import theory Fizzbuzz_Theory
  extern getfnval(int, int_fun) : int
  extern count(int_fun, int, int) : int

  meth sum(n: int) : int
    requires { n > 0 }
    ensures  { result = count(hmap, 0, n) }
    effects  { rd hmap, n }
end

module SumAB : B =
  meth sum(n: int) : int =
    var i: int in
    var v: int in
    result := 0;
    i := 0;
    while (i < n / 2) do
      invariant { 0 <= i /\ i <= n / 2 }
      invariant { result = count(hmap, 0, i) }
      v := getfnval(i, hmap);
      if (v = 1) then
        result := result + 1;
      end;
      i := i + 1;
    done;
    i := n / 2;
    while (i < n) do
      invariant { n / 2 <= i /\ i <= n }
      invariant { result = count(hmap, 0, n / 2) + count(hmap, n / 2, i) }
      v := getfnval(i, hmap);
      if (v = 1) then
        result := result + 1;
      end;
      i := i + 1;
    done;
    { result = count(hmap, 0, n / 2) + count(hmap, n / 2, n) };
    { result = count(hmap, 0, n) };
end

module SumBA : B =
  meth sum(n: int) : int =
    var i: int in
    var v: int in
    result := 0;
    i := n / 2;
    while (i < n) do
      invariant { n / 2 <= i /\ i <= n }
      invariant { result = count(hmap, n / 2, i) }
      v := getfnval(i, hmap);
      if (v = 1) then
        result := result + 1;
      end;
      i := i + 1;
    done;
    i := 0;
    while (i < n / 2) do
      invariant { 0 <= i /\ i <= n / 2 }
      invariant { result = count(hmap, n / 2, n) + count(hmap, 0, i) }
      v := getfnval(i, hmap);
      if (v = 1) then
        result := result + 1;
      end;
      i := i + 1;
    done;
    { result = count(hmap, n / 2, n) + count(hmap, 0, n / 2) };
    { result = count(hmap, 0, n) };
end

bimodule SumCommutes (SumAB | SumBA) =
  meth sum (n:int | n:int) : (int | int)
    requires { n =:= n }
    requires { Both (n > 0) }
    requires { forall i:int | i:int. Both (0 <= i /\ i < n)
               -> getfnval(i, hmap) =:= getfnval(i, hmap) }
    ensures  { result =:= result }
    effects  { rd hmap | rd hmap }
  = Var i:int | i:int in
    Var v:int | v:int in
    |_ result := 0 _|;
    /* Phase 1: left sums [0,n/2), right sums [n/2,n) */
    ( i := 0 | i := n / 2 );
    While (i < n / 2) | (i < n) . <| true <] | [> true |> do
      invariant { <| 0 <= i /\ i <= n / 2 <] }
      invariant { [> n / 2 <= i /\ i <= n |> }
      invariant { <| result = count(hmap, 0, i) <] }
      invariant { [> result = count(hmap, n / 2, i) |> }
      |_ v := getfnval(i, hmap) _|;
      If (v = 1) | (v = 1) then
        |_ result := result + 1 _|;
      end;
      |_ i := i + 1 _|;
    done;
    /* Phase 2: left sums [n/2,n), right sums [0,n/2) */
    ( i := n / 2 | i := 0 );
    While (i < n) | (i < n / 2) . <| true <] | [> true |> do
      invariant { <| n / 2 <= i /\ i <= n <] }
      invariant { [> 0 <= i /\ i <= n / 2 |> }
      invariant { <| result = count(hmap, 0, n / 2) + count(hmap, n / 2, i) <] }
      invariant { [> result = count(hmap, n / 2, n) + count(hmap, 0, i) |> }
      |_ v := getfnval(i, hmap) _|;
      If (v = 1) | (v = 1) then
        |_ result := result + 1 _|;
      end;
      |_ i := i + 1 _|;
    done;
    Assert { Both (result = count(hmap, 0, n)) };
end



bimodule SumCommutes_Seq (SumAB | SumBA) =
  meth sum (n:int | n:int) : (int | int)
    requires { n =:= n }
    requires { Both (n > 0) }
    requires { forall i:int | i:int. Both (0 <= i /\ i < n)
               -> getfnval(i, hmap) =:= getfnval(i, hmap) }
    ensures  { result =:= result }
    effects  { rd hmap | rd hmap }
  = Var i:int | i:int in
    Var v:int | v:int in
    |_ result := 0 _|;
    /* left sums both halves  */
    ( i := 0 | skip);
    (while (i < n / 2) do
      invariant {  0 <= i /\ i <= n / 2  }
      invariant {  result = count(hmap, 0, i)  }
      v := getfnval(i, hmap) ;
      if (v = 1)  then
        result := result + 1;
      end;
  
      i := i + 1 ;
    done | skip);
      
    ( i := n / 2 | skip);
    (while (i < n) do
    invariant {  n / 2 <= i /\ i <= n  }
    invariant { result = count(hmap, 0, n / 2) + count(hmap, n / 2, i) }
      v := getfnval(i, hmap) ;
      if (v = 1)  then
        result := result + 1;
      end;
  
      i := i + 1 ;
    done | skip);
    
    /* right sums both halves  */
    (skip | i := n / 2); 
    WhileR (i < n) do
      invariant { [> n / 2 <= i /\ i <= n |> }
      invariant { [> result = count(hmap, n / 2, i) |> }
      invariant { <| result = count(hmap, 0, n / 2) + count(hmap, n / 2, i) <] }
      (skip | v := getfnval(i, hmap)) ;
      (skip | if (v = 1)  then
            result := result + 1;
            end);
      
      (skip | i := i + 1);
    done;
    
      (skip | i := 0); 
  WhileR (i < n / 2) do
    invariant { <| result = count(hmap, 0, n / 2) + count(hmap, n / 2, i) <] }
    invariant { [> 0 <= i /\ i <= n / 2 |> }
    invariant { [> result = count(hmap, n / 2, n) + count(hmap, 0, i) |> }
    (skip | v := getfnval(i, hmap)) ;
      (skip | if (v = 1)  then
        result := result + 1;
      end);
        
      (skip | i := i + 1);
    done;


    Assert { Both (result = count(hmap, 0, n)) };
  
  end
    