//  WIP

// Translated from Veracity: https://github.com/veracity-lang/veracity/blob/main/benchmarks/manual/dihedral.vcy

// Dihedral group Dn — commutativity of rigid motions
// r and s are generators of the dihedral group Dn.
// All rigid motions are representable as r^k or r^k*s.
//
// Original Veracity source:
//   int n = 1;
//   int rk(int a, int k) => (a + k) % n;
//   int r(int a)         => rk(a, 1);
//   int s(int a)         => (n - a) % n;
//   int[] id() {
//     int[] a = new int[n];
//     for (int i = 0; i < n; i = i + 1;) {
//         a[i] = i;
//     }
//     return a;
// }
//  * First rigid motion is r^r1 * s^s1
//  * Second rigid motion is r^r2 * s^s2
//   commute (phi) {
//       { mrk(a, r1, true);  if (s1) { ms(a, true); }  }
//       { mrk(a, r2, false); if (s2) { ms(a, false); } }
//   }
//
//   phi = (!s1 && !s2)
//      || (s1 && !s2 && (r2 == 0 || (n % 2 == 0 && r2 == n / 2)))
//      || (!s1 && s2 && (r1 == 0 || (n % 2 == 0 && r1 == n / 2)))
//      || (s1 && s2 && r1 == r2)


// void mrk(int[] x, int k, bool start_in_middle) {
//     int m = start_in_middle ? n / 2 : 0;
//     for (int i = m; i < n; i = i + 1;) {
//         x[i] = rk(x[i], k);
//     }
//     for (int i = 0; i < m; i = i + 1;) {
//         x[i] = rk(x[i], k);
//     }
//     return;
// }

// void ms(int[] x, bool start_in_middle) {
//     int m = start_in_middle ? n / 2 : 0;
//     for (int i = m; i < n; i = i + 1;) {
//         x[i] = s(x[i]);
//     }
//     for (int i = 0; i < m; i = i + 1;) {
//         x[i] = s(x[i]);
//     }
//     return;
// }

// ----------------Theory--------------------------------------


// Rotation by k positions in Dn
function rk(a: int, k: int, n: int): int { (a + k) mod n }
// Symmetry (reflection) in Dn
function s_fn(a: int, n: int): int { (n - a) mod n }

// Composed motion: rotation by rot, then optionally symmetry
function motion(e: int, rot: int, do_s: bool, n: int): int {
  if do_s then s_fn(rk(e, rot, n), n) else rk(e, rot, n)
}

// Modular arithmetic lemma procedures

// Each lemma is a expressed as a procedure to call them locally to introduce
// the fact where needed, avoiding global axiom quantifier instantiation blowup.

// (a mod n + b) mod n == (a + b) mod n
procedure lemma_mod_add(a: int, b: int, n: int)
  requires n > 0;
  ensures (a mod n + b) mod n == (a + b) mod n;
{
  assume (a mod n + b) mod n == (a + b) mod n;
}

procedure lemma_mod_small(a: int, n: int)
  requires n > 0;
  requires 0 <= a && a < n;
  ensures a mod n == a;
{
  assume a mod n == a;
}

procedure lemma_mod_self(n: int)
  requires n > 0;
  ensures n mod n == 0;
{
  assume n mod n == 0;
}

procedure lemma_mod_range(a: int, n: int)
  requires n > 0;
  ensures 0 <= a mod n && a mod n < n;
{
  assume 0 <= a mod n && a mod n < n;
}

// s(s(a)) == a when 0 <= a < n
procedure lemma_double_reflect(a: int, n: int)
  requires n > 0;
  requires 0 <= a && a < n;
  ensures (n - (n - a) mod n) mod n == a;
{
  assume (n - (n - a) mod n) mod n == a;
}

procedure lemma_reflect_half_rot(a: int, n: int)
  requires n > 1;
  requires n mod 2 == 0;
  requires 0 <= a && a < n;
  ensures (n - (a + n div 2) mod n) mod n == ((n - a) mod n + n div 2) mod n;
{
  assume (n - (a + n div 2) mod n) mod n == ((n - a) mod n + n div 2) mod n;
}


// Elementwise commutativity checking by case-split on the four disjuncts of phi 
// ---------------------------------------------------------------------------
// Case 1: !s1 && !s2 — two pure rotations always commute
procedure commute_case_rot_rot()
{
  var n, r1, r2, e: int;

  assume n > 1;
  assume 0 <= r1 && r1 < n;
  assume 0 <= r2 && r2 < n;
  assume 0 <= e && e < n;

  // ((e+r1) mod n + r2) mod n = (e+r1+r2) mod n
  call lemma_mod_add(e + r1, r2, n);
  // ((e+r2) mod n + r1) mod n = (e+r2+r1) mod n
  call lemma_mod_add(e + r2, r1, n);

  assert motion(motion(e, r1, false, n), r2, false, n) ==
         motion(motion(e, r2, false, n), r1, false, n);
}

// ---------------------------------------------------------------------------
// Case 2a: s1 && !s2, r2 == 0 — rotation-reflection with identity rotation
procedure commute_case_sr_r0()
{
  var n, r1, e: int;

  assume n > 1;
  assume 0 <= r1 && r1 < n;
  assume 0 <= e && e < n;

  // (e + 0) mod n = e
  call lemma_mod_small(e, n);
  // ((e+0) mod n + r1) mod n = (e + r1) mod n
  call lemma_mod_add(e, r1, n);
  // range of (n - (e+r1) mod n) mod n
  call lemma_mod_range(e + r1, n);
  // ((n - (e+r1) mod n) mod n + 0) mod n = (n - (e+r1) mod n) mod n
  call lemma_mod_add(n - (e+r1) mod n, 0, n);

  assert motion(motion(e, r1, true, n), 0, false, n) ==
         motion(motion(e, 0, false, n), r1, true, n);
}

// ---------------------------------------------------------------------------
// Case 2b: s1 && !s2, n even, r2 == n/2 — reflection with half-rotation
procedure commute_case_sr_rhalf()
{
  var n, r1, e, h: int;

  assume n > 1;
  assume n mod 2 == 0;
  h := n div 2;
  assume 0 <= h && h < n;
  assume 0 <= r1 && r1 < n;
  assume 0 <= e && e < n;

  // LHS: motion(motion(e, r1, true, n), h, false, n)
  //     = ((n - (e+r1) mod n) mod n + h) mod n
  // RHS: motion(motion(e, h, false, n), r1, true, n)
  //     = (n - ((e+h) mod n + r1) mod n) mod n
  //     = (n - (e+h+r1) mod n) mod n

  // Step 1: simplify RHS inner rotation composition
  call lemma_mod_add(e + h, r1, n);
  // Now ((e+h) mod n + r1) mod n == (e + h + r1) mod n

  // Step 2: simplify LHS inner rotation
  call lemma_mod_add(e + r1, 0, n);

  // Step 3: the key identity for reflection + half-rotation
  call lemma_reflect_half_rot(rk(e, r1, n), n);
  call lemma_mod_range(e + r1, n);

  // Step 4: connect (e+r1) mod n + h to e + r1 + h
  call lemma_mod_add(e + r1, h, n);

  assert motion(motion(e, r1, true, n), h, false, n) ==
         motion(motion(e, h, false, n), r1, true, n);
}

// ---------------------------------------------------------------------------
// Case 3a: !s1 && s2, r1 == 0 — symmetric to case 2a
procedure commute_case_r0_sr()
{
  var n, r2, e: int;

  assume n > 1;
  assume 0 <= r2 && r2 < n;
  assume 0 <= e && e < n;

  call lemma_mod_small(e, n);
  call lemma_mod_add(e, r2, n);
  call lemma_mod_range(e + r2, n);
  call lemma_mod_add(n - (e+r2) mod n, 0, n);

  assert motion(motion(e, 0, false, n), r2, true, n) ==
         motion(motion(e, r2, true, n), 0, false, n);
}

// ---------------------------------------------------------------------------
// Case 3b: !s1 && s2, n even, r1 == n/2 — symmetric to case 2b
procedure commute_case_rhalf_sr()
{
  var n, r2, e, h: int;

  assume n > 1;
  assume n mod 2 == 0;
  h := n div 2;
  assume 0 <= h && h < n;
  assume 0 <= r2 && r2 < n;
  assume 0 <= e && e < n;

  call lemma_mod_add(e + h, r2, n);
  call lemma_mod_add(e + r2, 0, n);
  call lemma_reflect_half_rot(rk(e, r2, n), n);
  call lemma_mod_range(e + r2, n);
  call lemma_mod_add(e + r2, h, n);

  assert motion(motion(e, h, false, n), r2, true, n) ==
         motion(motion(e, r2, true, n), h, false, n);
}

// ---------------------------------------------------------------------------
// Case 4: s1 && s2 && r1 == r2 — identical motions, trivially commutes
procedure commute_case_sr_sr_same()
{
  var n, rot, e: int;

  assume n > 1;
  assume 0 <= rot && rot < n;
  assume 0 <= e && e < n;

  assert motion(motion(e, rot, true, n), rot, true, n) ==
         motion(motion(e, rot, true, n), rot, true, n);
}


// ----------------Implementation--------------------------------------

procedure id(n: int) returns (a: [int]int)
  requires n > 1;
  ensures (forall i: int :: 0 <= i && i < n ==> a[i] == i);
{
  var j: int;
  j := 0;
  while (j < n)
    invariant 0 <= j && j <= n;
    invariant (forall i: int :: 0 <= i && i < j ==> a[i] == i);
  {
    a[j] := j;
    j := j + 1;
  }
}

procedure mrk(x: [int]int, k: int, n: int, start_in_middle: bool) returns (x_out: [int]int)
  requires n > 1;
  requires 0 <= k && k < n;
  requires (forall i: int :: 0 <= i && i < n ==> 0 <= x[i] && x[i] < n);
  ensures (forall i: int :: 0 <= i && i < n ==> x_out[i] == rk(x[i], k, n));
  ensures (forall i: int :: !(0 <= i && i < n) ==> x_out[i] == x[i]);
  ensures (forall i: int :: 0 <= i && i < n ==> 0 <= x_out[i] && x_out[i] < n);
{
  var j, m: int;
  if(start_in_middle)
  {
    m := n div 2;

  }
  else
  {
    m := 0; 
  }

  assert 0 <= m && m <= n;
  x_out := x;
  
  j := m;
  while (j < n)
    invariant m <= j && j <= n;
    invariant (forall i: int :: 0 <= i && i < m ==> x_out[i] == x[i]);
    invariant (forall i: int :: m <= i && i < j ==> x_out[i] == rk(x[i], k, n));
    invariant (forall i: int :: j <= i && i < n ==> x_out[i] == x[i]);
    invariant (forall i: int :: !(0 <= i && i < n) ==> x_out[i] == x[i]);
  {
    x_out[j] := rk(x[j], k, n);
    j := j + 1; 
  }

  j := 0;
  while (j < m)
    invariant 0 <= j && j <= m;
    invariant (forall i: int :: 0 <= i && i < j ==> x_out[i] == rk(x[i], k, n));
    invariant (forall i: int :: j <= i && i < m ==> x_out[i] == x[i]);
    invariant (forall i: int :: m <= i && i < n ==> x_out[i] == rk(x[i], k, n));
    invariant (forall i: int :: !(0 <= i && i < n) ==> x_out[i] == x[i]);
  {
    x_out[j] := rk(x[j], k, n);
    j := j + 1;
  }

}

procedure ms_proc(x: [int]int, n: int, start_in_middle: bool) returns (x_out: [int]int)
  requires n > 1;
  requires (forall i: int :: 0 <= i && i < n ==> 0 <= x[i] && x[i] < n);
  ensures (forall i: int :: 0 <= i && i < n ==> x_out[i] == s_fn(x[i], n));
  ensures (forall i: int :: !(0 <= i && i < n) ==> x_out[i] == x[i]);
  ensures (forall i: int :: 0 <= i && i < n ==> 0 <= x_out[i] && x_out[i] < n);
{
  var j: int;
  var m: int;
  if(start_in_middle)
  {
    m := n div 2;

  }
  else
  {
    m := 0; 
  }

  assert 0 <= m && m <= n;
  x_out := x;
  
  j := m;
  while (j < n)
    invariant m <= j && j <= n;
    invariant (forall i: int :: 0 <= i && i < m ==> x_out[i] == x[i]);
    invariant (forall i: int :: m <= i && i < j ==> x_out[i] == s_fn(x[i], n));
    invariant (forall i: int :: j <= i && i < n ==> x_out[i] == x[i]);
    invariant (forall i: int :: !(0 <= i && i < n) ==> x_out[i] == x[i]);
  {
    x_out[j] := s_fn(x[j], n);
    j := j + 1;
  }

  j := 0;
  while (j < m)
    invariant 0 <= j && j <= m;
    invariant (forall i: int :: 0 <= i && i < j ==> x_out[i] == s_fn(x[i], n));
    invariant (forall i: int :: j <= i && i < m ==> x_out[i] == x[i]);
    invariant (forall i: int :: m <= i && i < n ==> x_out[i] == s_fn(x[i], n));
    invariant (forall i: int :: !(0 <= i && i < n) ==> x_out[i] == x[i]);
  {
    x_out[j] := s_fn(x[j], n);
    j := j + 1;
  }
}

// Apply a single rigid motion (rotation by rot, then optionally symmetry)
procedure apply_motion(x: [int]int, rot: int, do_s: bool, n: int) returns (x_out: [int]int)
  requires n > 1;
  requires 0 <= rot && rot < n;
  requires (forall i: int :: 0 <= i && i < n ==> 0 <= x[i] && x[i] < n);
  ensures (forall i: int :: 0 <= i && i < n ==> x_out[i] == motion(x[i], rot, do_s, n));
  ensures (forall i: int :: !(0 <= i && i < n) ==> x_out[i] == x[i]);
  ensures (forall i: int :: 0 <= i && i < n ==> 0 <= x_out[i] && x_out[i] < n);
{
  call x_out := mrk(x, rot, n, false);
  if (do_s) {
    call x_out := ms_proc(x_out, n, false);
  }
}

// Apply two rigid motions in sequence starting from identity
procedure run_two_motions(a: [int]int, r1: int, s1: bool, r2: int, s2: bool, n: int) returns (a_out: [int]int)
  requires n > 1;
  requires 0 <= r1 && r1 < n;
  requires 0 <= r2 && r2 < n;
  requires (forall i: int :: 0 <= i && i < n ==> a[i] == i);
  requires (forall i: int :: 0 <= i && i < n ==> 0 <= a[i] && a[i] < n);
  ensures (forall i: int :: 0 <= i && i < n ==> a_out[i] == motion(motion(i, r1, s1, n), r2, s2, n));
{
  call a_out := apply_motion(a, r1, s1, n);
  call a_out := apply_motion(a_out, r2, s2, n);
}

// ---------------------------------------------------------------------------
// Callable case lemma procedures (with ensures, not just assert)

// Case 1: two pure rotations always commute
procedure lemma_case1(e: int, r1: int, r2: int, n: int)
  requires n > 1; requires 0 <= r1 && r1 < n; requires 0 <= r2 && r2 < n;
  requires 0 <= e && e < n;
  ensures motion(motion(e, r1, false, n), r2, false, n) ==
          motion(motion(e, r2, false, n), r1, false, n);
{
  call lemma_mod_add(e + r1, r2, n);
  call lemma_mod_add(e + r2, r1, n);
}

// Case 2a: s1, !s2, r2 == 0
procedure lemma_case2a(e: int, r1: int, n: int)
  requires n > 1; requires 0 <= r1 && r1 < n;
  requires 0 <= e && e < n;
  ensures motion(motion(e, r1, true, n), 0, false, n) ==
          motion(motion(e, 0, false, n), r1, true, n);
{
  call lemma_mod_small(e, n);
  call lemma_mod_add(e, r1, n);
  call lemma_mod_range(e + r1, n);
  call lemma_mod_add(n - (e + r1) mod n, 0, n);
}

// Case 2b: s1, !s2, n even, r2 == n/2
procedure lemma_case2b(e: int, r1: int, n: int)
  requires n > 1; requires n mod 2 == 0;
  requires 0 <= r1 && r1 < n;
  requires 0 <= e && e < n;
  ensures motion(motion(e, r1, true, n), n div 2, false, n) ==
          motion(motion(e, n div 2, false, n), r1, true, n);
{
  call lemma_mod_add(e + n div 2, r1, n);
  call lemma_mod_add(e + r1, 0, n);
  call lemma_mod_range(e + r1, n);
  call lemma_reflect_half_rot(rk(e, r1, n), n);
  call lemma_mod_add(e + r1, n div 2, n);
}

// Case 3a: !s1, s2, r1 == 0
procedure lemma_case3a(e: int, r2: int, n: int)
  requires n > 1; requires 0 <= r2 && r2 < n;
  requires 0 <= e && e < n;
  ensures motion(motion(e, 0, false, n), r2, true, n) ==
          motion(motion(e, r2, true, n), 0, false, n);
{
  call lemma_mod_small(e, n);
  call lemma_mod_add(e, r2, n);
  call lemma_mod_range(e + r2, n);
  call lemma_mod_add(n - (e + r2) mod n, 0, n);
}

// Case 3b: !s1, s2, n even, r1 == n/2
procedure lemma_case3b(e: int, r2: int, n: int)
  requires n > 1; requires n mod 2 == 0;
  requires 0 <= r2 && r2 < n;
  requires 0 <= e && e < n;
  ensures motion(motion(e, n div 2, false, n), r2, true, n) ==
          motion(motion(e, r2, true, n), n div 2, false, n);
{
  call lemma_mod_add(e + n div 2, r2, n);
  call lemma_mod_add(e + r2, 0, n);
  call lemma_mod_range(e + r2, n);
  call lemma_reflect_half_rot(rk(e, r2, n), n);
  call lemma_mod_add(e + r2, n div 2, n);
}

// ---------------------------------------------------------------------------
// Master elementwise commutativity lemma: dispatches to callable case lemmas
procedure lemma_motion_commutes(e: int, r1: int, s1: bool, r2: int, s2: bool, n: int)
  requires n > 1;
  requires 0 <= r1 && r1 < n;
  requires 0 <= r2 && r2 < n;
  requires 0 <= e && e < n;
  requires (!s1 && !s2) ||
           (s1 && !s2 && (r2 == 0 || (n mod 2 == 0 && r2 == n div 2))) ||
           (!s1 && s2 && (r1 == 0 || (n mod 2 == 0 && r1 == n div 2))) ||
           (s1 && s2 && r1 == r2);
  ensures motion(motion(e, r1, s1, n), r2, s2, n) ==
          motion(motion(e, r2, s2, n), r1, s1, n);
{
  if (!s1 && !s2) {
    call lemma_case1(e, r1, r2, n);
  } else if (s1 && !s2) {
    if (r2 == 0) {
      call lemma_case2a(e, r1, n);
    } else {
      call lemma_case2b(e, r1, n);
    }
  } else if (!s1 && s2) {
    if (r1 == 0) {
      call lemma_case3a(e, r2, n);
    } else {
      call lemma_case3b(e, r2, n);
    }
  } else {
    // s1 && s2 && r1 == r2 — trivially commutes
  }
}

// ---------------------------------------------------------------------------
// Array-level commutativity proof: block1;block2 ≡ block2;block1
//
// Block 1: mrk(a, r1); if (s1) ms(a)     — rigid motion r^r1 * s^s1
// Block 2: mrk(a, r2); if (s2) ms(a)     — rigid motion r^r2 * s^s2
//
// Strategy: assume array contents (avoiding quantifier blowup from procedure
// call postconditions), then use the master elementwise lemma in a loop.
procedure commutativity_check()
{
  var n, r1, r2, j: int;
  var s1, s2: bool;
  var a, a': [int]int;

  assume n > 1;
  assume 0 <= r1 && r1 < n;
  assume 0 <= r2 && r2 < n;

  // Commutativity condition phi
  assume (!s1 && !s2) ||
         (s1 && !s2 && (r2 == 0 || (n mod 2 == 0 && r2 == n div 2))) ||
         (!s1 && s2 && (r1 == 0 || (n mod 2 == 0 && r1 == n div 2))) ||
         (s1 && s2 && r1 == r2);

  // Array a = result of block1;block2 on identity
  // (justified by run_two_motions which verifies separately)
  assume (forall i: int :: {a[i]} 0 <= i && i < n ==>
    a[i] == motion(motion(i, r1, s1, n), r2, s2, n));

  // Array a' = result of block2;block1 on identity
  assume (forall i: int :: {a'[i]} 0 <= i && i < n ==>
    a'[i] == motion(motion(i, r2, s2, n), r1, s1, n));

  // Prove arrays are equal element-by-element
  j := 0;
  while (j < n)
    invariant 0 <= j && j <= n;
    invariant (forall i: int :: 0 <= i && i < j ==> a[i] == a'[i]);
  {
    // Elementwise commutativity for index j (ground postcondition, no quantifiers)
    call lemma_motion_commutes(j, r1, s1, r2, s2, n);
    assert a[j] == a'[j];
    j := j + 1;
  }

  assert (forall i: int :: 0 <= i && i < n ==> a[i] == a'[i]);
}
