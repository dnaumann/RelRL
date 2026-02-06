interface T =
  import theory Tiling_theory
  extern f (int) : int

  class IntArray { length: int; slots: int array; }
  class IntArray2 { tDlength: int; tDslots: IntArray array; }

  public a1: IntArray
  public a2: IntArray2

  public n: int
  public m: int

  predicate okGlobals() =
       a1 <> null
    /\ a2 <> null
    /\ n > 0
    /\ m > 0
    /\ a1.length = n * m 
    /\ a2.tDlength = n
    /* Each ref in tDslots points to a non-null IntArray with length m */
    /\ (forall i:int. 0 <= i /\ i < n ->
          let row_i = a2[i] in row_i <> null /\ row_i.length = m)
    /* No aliasing in a2 -- refs in tDslots are unique */
    /\ (forall i:int. 0 <= i /\ i < n -> forall j:int. 0 <= j /\ j < n ->
          i <> j ->
          let row_i = a2[i] in let row_j = a2[j] in row_i <> row_j)

  meth prog () : unit
    requires { okGlobals() }
    effects  { rw alloc, {a1}`slots, {a2}`tDslots`slots; 
               rd a1, a2, n, m, {a2}`tDslots }
end

module M0 : T =
  class IntArray { length: int; slots: int array; }
  class IntArray2 { tDlength: int; tDslots: IntArray array; }

  meth prog () : unit
    ensures { forall i:int. let len = a1.length in 
                0 <= i /\ i < len -> a1[i] = f(i) }
  = var x: int in
    x := 0;
    while (x < n * m) do
      invariant {0 <= x /\ x <= n * m }
      invariant { forall i:int. 0 <= i /\ i < x -> a1[i] = f(i) }
      effects { rw {a1}`slots }
      a1[x] := f(x);
      x := x+1;
      while (x < m * n && x mod m <> 0) do
        invariant {0 <= x /\ x <= n * m }
        invariant { forall i:int. 0 <= i /\ i < x -> a1[i] = f(i) }
        effects { rw {a1}`slots }
        a1[x] := f(x);
        x := x+1;
      done;
    done;
end

module M1 : T =
  class IntArray { length: int; slots: int array; }
  class IntArray2 { tDlength: int; tDslots: IntArray array; }
 
  meth prog () : unit
    ensures { forall i:int. 0 <= i /\ i < n ->
                let row_i = a2[i] in
                forall j:int. 0 <= j /\ j < m -> row_i[j] = f(i*m+j) }
  = var i: int in
    var j: int in
    var row_i: IntArray in
    i := 0;
    while (i < n) do
      invariant { 0 <= i /\ i <= n }
      invariant { forall p:int. 0 <= p /\ p < i ->
        let row_p = a2[p] in
        forall j:int. 0 <= j /\ j < m -> row_p[j] = f(p*m+j) }
      effects { rw {a2}`tDslots`slots; rd {a2}`tDslots }
      j := 0;
      if (j < m) then
        /* a2[i,j] := f(i*M+j) */
        row_i := a2[i]; row_i[j] := f(i*m+j);
        j := j+1;
      end;
      while (j < m) do
        invariant { 0 <= i /\ i <= n }
        invariant { 0 <= j /\ j <= m }
        invariant { forall p:int. 0 <= p /\ p < i ->
          let row_p = a2[p] in
          forall j:int. 0 <= j /\ j < m -> row_p[j] = f(p*m+j) }
        invariant { forall q:int. 0 <= q /\ q < j ->
          let row_i = a2[i] in row_i[q] = f(i*m+q) }
        effects { rw {a2}`tDslots`slots; rd {a2}`tDslots }
        /* a2[i,j] := f(i*M+j) */
        row_i := a2[i]; row_i[j] := f(i*m+j);
        j := j+1;
      done;
      i := i+1;
    done;

end

bimodule BM (M0 | M1) =

  /* R(x,i,j) = 
       forall l,r,o. 0 <= l < x /\ 0 <= r < i /\ 0 <= o < j /\ l = r*M + o
                     ==> a1[l] =:= a2[r,o]
         where M is the length of each row in a2.

     spec   prog|prog: Agree n /\ Agree m ==>>  R(n*m,n,m) */

  predicate tilingInv (x:int | i:int,j:int) =
    forall l:int | r:int, o:int.
      <| 0 <= l /\ l < x <] ->
      [> 0 <= r /\ r < i /\ 0 <= o /\ o < j |> ->
      [< l <] = [> i*m + j >] ->
      let lftv | = a1[l] in
      let | row  = a2[r] in
      let | rgtv = row[o] in
      [< lftv <] = [> rgtv >]

  meth prog (|) : (unit|unit)
    requires { Agree n /\ Agree m }
    requires { Both(okGlobals()) }
    ensures  { tilingInv(n*m|n,m) }
  = Var x:int| in
    Var |i:int in
    Var |j:int in
    Var |row_i:IntArray in
    ( x := 0 | i := 0 );
    While (x < n*m) | (i < n) . do
      invariant { <| 0 <= x /\ x <= n*m <] }
      invariant { [> 0 <= i /\ i <= n |> }
      invariant { [< x <] = [> i*m >] }
      invariant { tilingInv(x|i,0) }
      
      ( skip | j:=0 );
      ( a1[x] := f(x); x:=x+1
      | if (j < m) then row_i := a2[i]; row_i[j] := f(i*m+j); j:=j+1 end );

      While (x < m*n && x mod m <> 0) | (j < m) . do
        invariant { <| 0 <= x /\ x <= n*m <] }
        invariant { [> 0 <= i /\ i <= n /\ 0 <= j /\ j <= m |> }
        invariant { [< x <] = [> i*m+j >] }
        invariant { tilingInv(x|i,j) }

        ( a1[x] := f(x); x:=x+1
        | row_i := a2[i]; row_i[j] := f(i*m+j); j:=j+1 );

      done;
      ( skip | i:=i+1 );
    done;

end
