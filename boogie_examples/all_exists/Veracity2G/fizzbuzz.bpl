var $hmap : [int] int;
var $hmap' : [int] int;

function count(a: [int]int, lo: int, hi: int): int;
axiom (forall a: [int]int, k: int :: { count(a, k, k) }
  count(a, k, k) == 0);
axiom (forall a: [int]int, lo: int, hi: int :: { count(a, lo, hi) }
  lo < hi ==>
  count(a, lo, hi) == count(a, lo, hi-1) + (if a[hi-1] == 1 then 1 else 0));
axiom (forall a: [int]int, lo: int, mid: int, hi: int ::
  { count(a, lo, mid), count(a, mid, hi) }
  lo <= mid && mid <= hi ==>
  count(a, lo, hi) == count(a, lo, mid) + count(a, mid, hi));
axiom (forall a: [int]int, b: [int]int, lo: int, hi: int ::
  { count(a, lo, hi), count(b, lo, hi) }
  (forall k: int :: lo <= k && k < hi ==> a[k] == b[k]) ==>
  count(a, lo, hi) == count(b, lo, hi));

procedure sumbi (n: int, n': int) returns (total, total': int)
  requires n == n';
  requires n > 0;
  requires (forall i: int :: 0 <= i && i < n ==> (i mod 3 == 0 || i mod 5 == 0) ==> $hmap'[i] == 1);
  requires (forall i: int :: 0 <= i && i < n ==> !(i mod 3 == 0 || i mod 5 == 0) ==> $hmap'[i] == 0);
  requires (forall i: int :: 0 <= i && i < n ==> $hmap[i] == $hmap'[i]);
  ensures total == total';
{
  var i : int; var i' : int;
  var vsnap: int;

  total := 0; total' := 0;

  //A; B

  i := 0;
  while (i < n div 2)
    invariant 0 <= i && i <= n div 2;
    invariant total == count($hmap, 0, i);
  {
    if ($hmap[i] == 1)
    {
      total := total + 1 ;
    }

    i := i + 1;

  }

  i := n div 2;
  while (i < n)
    invariant n div 2 <= i && i <= n;
    invariant total == count($hmap, 0, n div 2) + count($hmap, n div 2, i);
  {
    if ($hmap[i] == 1)
    {
      total := total + 1 ;
    }

    i := i + 1;
  }

  //B; A

  i' := n div 2;
  while (i' < n)
    invariant n div 2 <= i' && i' <= n;
    invariant total' == count($hmap', n div 2, i');
  {
    vsnap := n - i'; // variant 

    if ($hmap'[i'] == 1)
    {
      total' := total' + 1;
    }

    i' := i' + 1;

    assert (0 <= (n - i') && (n - i') < vsnap); // variant decreases
  }

  i' := 0;
  while (i' < n div 2)
    invariant 0 <= i' && i' <= n div 2;
    invariant total' == count($hmap', n div 2, n) + count($hmap', 0, i');
  {
    vsnap := (n div 2) - i'; // variant 

    if ($hmap'[i'] == 1)
    {
      total' := total' + 1;
    }

    i' := i' + 1;

    assert (0 <= ((n div 2) - i') && ((n div 2) - i') < vsnap); // variant decreases
  }

  assert total == count($hmap, 0, n div 2) + count($hmap, n div 2, n);
  assert total == count($hmap, 0, n);
  assert total' == count($hmap', n div 2, n) + count($hmap', 0, n div 2);
  assert total' == count($hmap', 0, n);
  assert count($hmap, 0, n) == count($hmap', 0, n);
}

procedure bi (n: int, n': int) returns ()
  requires n == n';
  requires n > 0;
  requires (forall i: int :: 0 <= i && i < n ==> $hmap[i] == 0);
  requires (forall i: int :: 0 <= i && i < n' ==> $hmap'[i] == 0);
  ensures (forall i: int :: 0 <= i && i < n ==> (i mod 3 == 0 || i mod 5 == 0) ==> $hmap'[i] == 1);
  ensures (forall i: int :: 0 <= i && i < n ==> !(i mod 3 == 0 || i mod 5 == 0) ==> $hmap'[i] == 0);
  ensures (forall i: int :: 0 <= i && i < n ==> $hmap[i] == $hmap'[i]);
  modifies $hmap, $hmap';
{
  var i: int; var i': int;
  var vsnap: int;

  // Program 1
  i := 0;
  while (i < n)
    invariant (0 <= i && i <= n);
    invariant (forall j: int :: 0 <= j && j < n && !(j mod 3 == 0) ==> $hmap[j] == 0);
    invariant (forall j: int :: 0 <= j && j < i ==> (j mod 3 == 0 <==> $hmap[j] == 1));
  {
    if (i mod 3 == 0) { $hmap[i] := 1; }
    i := i + 1;
  }
  assert (forall j: int :: 0 <= j && j < n && j mod 3 == 0 ==> $hmap[j] == 1);
  i := 0;
  while (i < n)
    invariant (0 <= i && i <= n);
    invariant (forall j: int :: 0 <= j && j < n && j mod 3 == 0 ==> $hmap[j] == 1);
    invariant (forall j: int :: 0 <= j && j < i && j mod 5 == 0 ==> $hmap[j] == 1);
    invariant (forall j: int :: 0 <= j && j < n && !(j mod 3 == 0 || j mod 5 == 0) ==> $hmap[j] == 0);
  {
    if (i mod 5 == 0) { $hmap[i] := 1; } i := i + 1;
  }
  assert (forall j: int :: 0 <= j && j < n ==> ((j mod 3 == 0 || j mod 5 == 0) <==> $hmap[j] == 1));
  // Program 2
  assert (forall i: int :: 0 <= i && i < n' ==> $hmap'[i] == 0);
  i' := 0;
  while (i' < n')
    invariant (0 <= i' && i' <= n');
    invariant (forall j': int :: 0 <= j' && j' < n' && !(j' mod 5 == 0) ==> $hmap'[j'] == 0);
    invariant (forall j': int :: 0 <= j' && j' < i' && j' mod 5 == 0 ==> $hmap'[j'] == 1);
  {
    vsnap := n' - i'; // variant

    if (i' mod 5 == 0) {
      $hmap'[i'] := 1;
    }
    i' := i' + 1;

    assert (0 <= (n' - i') && (n' - i') < vsnap); // variant decreases
  }
  assert (forall j': int :: 0 <= j' && j' < n' && j' mod 5 == 0 ==> $hmap'[j'] == 1);
  i' := 0;
  while (i' < n')
    invariant (0 <= i' && i' <= n');
    invariant (forall j': int :: 0 <= j' && j' < n' && j' mod 5 == 0 ==> $hmap'[j'] == 1);
    invariant (forall j': int :: 0 <= j' && j' < i' && j' mod 3 == 0 ==> $hmap'[j'] == 1);
    invariant (forall j': int :: 0 <= j' && j' < n' && !(j' mod 3 == 0 || j' mod 5 == 0) ==> $hmap'[j'] == 0);
  {
    vsnap := n' - i'; // variant 
    
    if (i' mod 3 == 0) {
      $hmap'[i'] := 1;
    }
    i' := i' + 1;

    assert (0 <= (n' - i') && (n' - i') < vsnap); // variant decreases
  }
  assert (forall j: int :: 0 <= j && j < n && !(j mod 3 == 0 || j mod 5 == 0) ==> $hmap[j] == 0);
  assert (forall j: int :: 0 <= j && j < n && (j mod 3 == 0 || j mod 5 == 0) ==> $hmap[j] == 1);
  assert (forall j: int :: 0 <= j && j < n && !(j mod 3 == 0 || j mod 5 == 0) ==> $hmap'[j] == 0);
  assert (forall j': int :: 0 <= j' && j' < n' && (j' mod 3 == 0 || j' mod 5 == 0) ==> $hmap'[j'] == 1);
}
procedure f1 (n: int) returns ()
  requires (forall i: int :: $hmap[i] == 0);
  requires n > 0;
  ensures (forall i: int :: 0 <= i && i < n && (i mod 3 == 0 || i mod 5 == 0) ==>
             $hmap[i] == 1);
  modifies $hmap;
{
  var i: int;
  i := 0;
  while (i < n)
    invariant (0 <= i && i <= n);
    invariant (forall j: int :: 0 <= j && j < i && j mod 3 == 0 ==>
                          $hmap[j] == 1);
  {
    if (i mod 3 == 0) {
      $hmap[i] := 1;
    }
    i := i + 1;
  }
  assert (forall j: int :: 0 <= j && j < n && j mod 3 == 0 ==> $hmap[j] == 1);
  i := 0;
  while (i < n)
    invariant (0 <= i && i <= n);
    invariant (forall j: int :: 0 <= j && j < n && j mod 3 == 0 ==> $hmap[j] == 1);
    invariant (forall j: int ::
      0 <= j && j < i && j mod 5 == 0 ==>
      $hmap[j] == 1);
  {
    if (i mod 5 == 0) {
      $hmap[i] := 1;
    }
    i := i + 1;
  }
  assert (forall j: int :: 0 <= j && j < n && (j mod 3 == 0 || j mod 5 == 0) ==> $hmap[j] == 1);
}
procedure f2 (n: int) returns ()
  requires (forall i: int :: $hmap[i] == 0);
  requires n > 0;
  ensures (forall i: int :: 0 <= i && i < n && (i mod 3 == 0 || i mod 5 == 0) ==>
             $hmap[i] == 1);
  modifies $hmap;
{
  var i: int;
  i := 0;
  while (i < n)
    invariant (0 <= i && i <= n);
    invariant (forall j: int ::
      0 <= j && j < i && j mod 5 == 0 ==>
      $hmap[j] == 1);
  {
    if (i mod 5 == 0) {
      $hmap[i] := 1;
    }
    i := i + 1;
  }
  assert (forall j: int :: 0 <= j && j < n && j mod 5 == 0 ==> $hmap[j] == 1);
  i := 0;
  while (i < n)
    invariant (0 <= i && i <= n);
    invariant (forall j: int :: 0 <= j && j < n && j mod 5 == 0 ==> $hmap[j] == 1);
    invariant (forall j: int :: 0 <= j && j < i && j mod 3 == 0 ==>
                          $hmap[j] == 1);
  {
    if (i mod 3 == 0) {
      $hmap[i] := 1;
    }
    i := i + 1;
  }
  assert (forall j: int :: 0 <= j && j < n && (j mod 3 == 0 || j mod 5 == 0) ==> $hmap[j] == 1);
}
