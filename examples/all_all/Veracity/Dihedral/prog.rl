/* Translated from Veracity: https://github.com/veracity-lang/veracity/blob/main/benchmarks/manual/dihedral.vcy */

/* Dihedral group Dn — commutativity of rigid motions.
   r and s are generators of the dihedral group Dn.
   All rigid motions are representable as r^k or r^k*s.

   Block 1: mrk(a, r1); if (s1) { ms(a); }   — rigid motion r^r1 * s^s1
   Block 2: mrk(a, r2); if (s2) { ms(a); }   — rigid motion r^r2 * s^s2

   phi = (s1 = false /\ s2 = false)
      \/ (s1 = true /\ s2 = false /\ (r2 = 0 \/ (n mod 2 = 0 /\ r2 = n / 2)))
      \/ (s1 = false /\ s2 = true /\ (r1 = 0 \/ (n mod 2 = 0 /\ r1 = n / 2)))
      \/ (s1 = true /\ s2 = true /\ r1 = r2)
*/

interface DIHEDRAL =
  import theory Dihedral_Theory
  extern rk(int, int, int) : int
  extern s_fn(int, int) : int
  extern motion(int, int, bool, int) : int

  class IntArray { length: int; slots: int array; }

  public a : IntArray
  public n : int
  public r1 : int
  public r2 : int
  public s1 : bool
  public s2 : bool

  meth main () : unit
    requires { a <> null /\ a.length = n }
    requires { n > 1 }
    requires { 0 <= r1 /\ r1 < n }
    requires { 0 <= r2 /\ r2 < n }
    requires { forall i:int. 0 <= i /\ i < n -> a[i] = i }
    requires { forall i:int. 0 <= i /\ i < n ->
                 let v = a[i] in 0 <= v /\ v < n }
    /* Commutativity condition phi */
    requires { (s1 = false /\ s2 = false)
            \/ (s1 = true /\ s2 = false /\ (r2 = 0 \/ (n mod 2 = 0 /\ r2 = n / 2)))
            \/ (s1 = false /\ s2 = true /\ (r1 = 0 \/ (n mod 2 = 0 /\ r1 = n / 2)))
            \/ (s1 = true /\ s2 = true /\ r1 = r2) }
    ensures  { forall i:int. 0 <= i /\ i < n ->
                 let v = a[i] in 0 <= v /\ v < n }
    effects  { rd a, n, r1, r2, s1, s2, {a}`length; wr {a}`slots }
end

/* Left execution: block1 then block2 */
module M0 : DIHEDRAL =
  class IntArray { length: int; slots: int array; }

  meth main () : unit 
   
end

/* Right execution: block2 then block1 */
module M1 : DIHEDRAL =
  class IntArray { length: int; slots: int array; }

  meth main () : unit 
end

/* Relational proof: block1;block2 = block2;block1
   Left  (M0): block1 then block2
   Right (M1): block2 then block1
   Both start from the same identity array and produce the same result
   under the commutativity condition phi. */
bimodule COMMUTE (M0 | M1) =

  meth main (|) : (unit | unit)
    requires { Both (a <> null /\ a.length = n) }
    requires { Both (n > 1) }
    requires { Both (0 <= r1 /\ r1 < n) }
    requires { Both (0 <= r2 /\ r2 < n) }
    requires { Both (forall i:int. 0 <= i /\ i < n -> a[i] = i) }
    requires { Both (forall i:int. 0 <= i /\ i < n ->
                       let v = a[i] in 0 <= v /\ v < n) }
    requires { Both (
                 (s1 = false /\ s2 = false)
              \/ (s1 = true /\ s2 = false /\ (r2 = 0 \/ (n mod 2 = 0 /\ r2 = n / 2)))
              \/ (s1 = false /\ s2 = true /\ (r1 = 0 \/ (n mod 2 = 0 /\ r1 = n / 2)))
              \/ (s1 = true /\ s2 = true /\ r1 = r2) ) }
    requires { Agree a /\ Agree n /\ Agree r1 /\ Agree r2 /\ Agree s1 /\ Agree s2 }
    requires { Agree {a}`any }
    ensures  { Agree {a}`slots }
    effects  { rd a, n, r1, r2, s1, s2, {a}`length; wr {a}`slots
             | rd a, n, r1, r2, s1, s2, {a}`length; wr {a}`slots }
  = Var i: int | i: int in
    Var tmp: int | tmp: int in

    /* Phase 1: Left runs block 1 alone, right idles */
    ( /* Left: block 1 — mrk(a, r1) then if (s1) ms(a) */
      i := 0;
      while (i < n) do
        invariant { 0 <= i /\ i <= n }
        invariant { forall m:int. 0 <= m /\ m < i ->
                      a[m] = rk(m, r1, n) }
        invariant { forall m:int. i <= m /\ m < n -> a[m] = m }
        invariant { forall m:int. 0 <= m /\ m < n ->
                      let v = a[m] in 0 <= v /\ v < n }
        effects { wr {a}`slots }
        a[i] := ((i + r1) mod n);
        i := i + 1;
      done;
      if (s1) then
        i := 0;
        while (i < n) do
          invariant { 0 <= i /\ i <= n }
          invariant { forall m:int. 0 <= m /\ m < i ->
                        a[m] = s_fn(rk(m, r1, n), n) }
          invariant { forall m:int. i <= m /\ m < n ->
                        a[m] = rk(m, r1, n) }
          invariant { forall m:int. 0 <= m /\ m < n ->
                        let v = a[m] in 0 <= v /\ v < n }
          effects { wr {a}`slots }
          tmp := a[i];
          a[i] := ((n - tmp) mod n);
          i := i + 1;
        done;
      else
        skip;
      end
    | /* Right: idle */
      skip
    );

    /* Phase 1 result: left has motion(m,r1,s1,n), right still identity */
    Assert { <| forall m:int. 0 <= m /\ m < n ->
                  a[m] = motion(m, r1, s1, n) <] };
    Assert { <| forall m:int. 0 <= m /\ m < n ->
                  let v = a[m] in 0 <= v /\ v < n <] };

    /* Phase 2: Lockstep block 2 — mrk(a, r2) then if (s2) ms(a) */
    |_ i := 0 _|;
    While (i < n) | (i < n) . <| false <] | [> false |> do
      invariant { i =:= i }
      invariant { Both (0 <= i /\ i <= n) }
      /* Left: processed elements got r2 rotation on top of motion(m,r1,s1,n) */
      invariant { <| forall m:int. 0 <= m /\ m < i ->
                        a[m] = rk(motion(m, r1, s1, n), r2, n) <] }
      /* Left: unprocessed elements still hold Phase 1 result */
      invariant { <| forall m:int. i <= m /\ m < n ->
                        a[m] = motion(m, r1, s1, n) <] }
      /* Right: processed elements got r2 rotation on identity */
      invariant { [> forall m:int. 0 <= m /\ m < i ->
                        a[m] = rk(m, r2, n) |> }
      /* Right: unprocessed elements still identity */
      invariant { [> forall m:int. i <= m /\ m < n -> a[m] = m |> }
      invariant { Both (forall m:int. 0 <= m /\ m < n ->
                          let v = a[m] in 0 <= v /\ v < n) }
      effects { wr {a}`slots | wr {a}`slots }
      |_ tmp := a[i] _|;
      |_ a[i] := ((tmp + r2) mod n) _|;
      |_ i := i + 1 _|;
    done;

    If (s2) | (s2) then
      |_ i := 0 _|;
      While (i < n) | (i < n) . <| false <] | [> false |> do
        invariant { i =:= i }
        invariant { Both (0 <= i /\ i <= n) }
        /* Left: processed = full motion(motion(m,r1,s1,n),r2,true,n) */
        invariant { <| forall m:int. 0 <= m /\ m < i ->
                          a[m] = s_fn(rk(motion(m, r1, s1, n), r2, n), n) <] }
        /* Left: unprocessed = still just rotated */
        invariant { <| forall m:int. i <= m /\ m < n ->
                          a[m] = rk(motion(m, r1, s1, n), r2, n) <] }
        /* Right: processed = s_fn(rk(m,r2,n),n) */
        invariant { [> forall m:int. 0 <= m /\ m < i ->
                          a[m] = s_fn(rk(m, r2, n), n) |> }
        /* Right: unprocessed = still just rotated */
        invariant { [> forall m:int. i <= m /\ m < n ->
                          a[m] = rk(m, r2, n) |> }
        invariant { Both (forall m:int. 0 <= m /\ m < n ->
                            let v = a[m] in 0 <= v /\ v < n) }
        effects { wr {a}`slots | wr {a}`slots }
        |_ tmp := a[i] _|;
        |_ a[i] := ((n - tmp) mod n) _|;
        |_ i := i + 1 _|;
      done
    end;

    /* After Phase 2: bridge to motion form */
    Assert { <| forall m:int. 0 <= m /\ m < n ->
                  a[m] = motion(motion(m, r1, s1, n), r2, s2, n) <] };
    Assert { [> forall m:int. 0 <= m /\ m < n ->
                  a[m] = motion(m, r2, s2, n) |> };

    /* Phase 3: Right runs block 1 alone, left idles */
    ( /* Left: idle */
      skip
    | /* Right: block 1 — mrk(a, r1) then if (s1) ms(a) */
      i := 0;
      while (i < n) do
        invariant { 0 <= i /\ i <= n }
        /* processed: applied r1 rotation on top of motion(m,r2,s2,n) */
        invariant { forall m:int. 0 <= m /\ m < i ->
                      a[m] = rk(motion(m, r2, s2, n), r1, n) }
        /* unprocessed: still Phase 2 result */
        invariant { forall m:int. i <= m /\ m < n ->
                      a[m] = motion(m, r2, s2, n) }
        invariant { forall m:int. 0 <= m /\ m < n ->
                      let v = a[m] in 0 <= v /\ v < n }
        effects { wr {a}`slots }
        tmp := a[i];
        a[i] := ((tmp + r1) mod n);
        i := i + 1;
      done;
      if (s1) then
        i := 0;
        while (i < n) do
          invariant { 0 <= i /\ i <= n }
          /* processed: full motion(motion(m,r2,s2,n),r1,true,n) */
          invariant { forall m:int. 0 <= m /\ m < i ->
                        a[m] = s_fn(rk(motion(m, r2, s2, n), r1, n), n) }
          /* unprocessed: still just rotated */
          invariant { forall m:int. i <= m /\ m < n ->
                        a[m] = rk(motion(m, r2, s2, n), r1, n) }
          invariant { forall m:int. 0 <= m /\ m < n ->
                        let v = a[m] in 0 <= v /\ v < n }
          effects { wr {a}`slots }
          tmp := a[i];
          a[i] := ((n - tmp) mod n);
          i := i + 1;
        done;
      else
        skip;
      end
    );

    /* After Phase 3: both sides expressed via motion */
    Assert { <| forall m:int. 0 <= m /\ m < n ->
                  a[m] = motion(motion(m, r1, s1, n), r2, s2, n) <] };
    Assert { [> forall m:int. 0 <= m /\ m < n ->
                  a[m] = motion(motion(m, r2, s2, n), r1, s1, n) |> };

    /* Bridge: case-by-case commutativity from the theory lemmas */
    Assert { Both (forall m:int. 0 <= m /\ m < n ->
                     not s1 /\ not s2 ->
                     motion(motion(m, r1, false, n), r2, false, n) =
                     motion(motion(m, r2, false, n), r1, false, n)) };
    Assert { Both (forall m:int. 0 <= m /\ m < n ->
                     s1 /\ not s2 /\ r2 = 0 ->
                     motion(motion(m, r1, true, n), 0, false, n) =
                     motion(motion(m, 0, false, n), r1, true, n)) };
    Assert { Both (forall m:int. 0 <= m /\ m < n ->
                     s1 /\ not s2 /\ r2 = n / 2 ->
                     motion(motion(m, r1, true, n), (n / 2), false, n) =
                     motion(motion(m, (n / 2), false, n), r1, true, n)) };
    Assert { Both (forall m:int. 0 <= m /\ m < n ->
                     not s1 /\ s2 /\ r1 = 0 ->
                     motion(motion(m, 0, false, n), r2, true, n) =
                     motion(motion(m, r2, true, n), 0, false, n)) };
    Assert { Both (forall m:int. 0 <= m /\ m < n ->
                     not s1 /\ s2 /\ r1 = n / 2 ->
                     motion(motion(m, (n / 2), false, n), r2, true, n) =
                     motion(motion(m, r2, true, n), (n / 2), false, n)) };
    Assert { Both (forall m:int. 0 <= m /\ m < n ->
                     s1 /\ s2 /\ r1 = r2 ->
                     motion(motion(m, r1, true, n), r1, true, n) =
                     motion(motion(m, r1, true, n), r1, true, n)) };

    /* Consolidated bridge: under phi, composed motions commute pointwise. */
    Assert { Both (forall m:int. 0 <= m /\ m < n ->
                     ((s1 = false /\ s2 = false)
                   \/ (s1 = true /\ s2 = false /\ (r2 = 0 \/ (n mod 2 = 0 /\ r2 = n / 2)))
                   \/ (s1 = false /\ s2 = true /\ (r1 = 0 \/ (n mod 2 = 0 /\ r1 = n / 2)))
                   \/ (s1 = true /\ s2 = true /\ r1 = r2)) ->
                     motion(motion(m, r1, s1, n), r2, s2, n) =
                     motion(motion(m, r2, s2, n), r1, s1, n)) };
end
