var $hmap : [int] int;
var $hmap' : [int] int;
procedure bi (n: int, n': int) returns ()
  requires n == n';
  requires n > 0;
  requires (forall i: int :: 0 <= i && i < n ==> $hmap[i] == 0);
  requires (forall i: int :: 0 <= i && i < n' ==> $hmap'[i] == 0);
  ensures (forall i: int :: 0 <= i && i < n ==> $hmap[i] == $hmap'[i]);
  modifies $hmap, $hmap';
{
  var i: int; var i': int;
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
    if (i' mod 5 == 0) {
      $hmap'[i'] := 1;
    }
    i' := i' + 1;
  }
  assert (forall j': int :: 0 <= j' && j' < n' && j' mod 5 == 0 ==> $hmap'[j'] == 1);
  i' := 0;
  while (i' < n')
    invariant (0 <= i' && i' <= n');
    invariant (forall j': int :: 0 <= j' && j' < n' && j' mod 5 == 0 ==> $hmap'[j'] == 1);
    invariant (forall j': int :: 0 <= j' && j' < i' && j' mod 3 == 0 ==> $hmap'[j'] == 1);
    invariant (forall j': int :: 0 <= j' && j' < n' && !(j' mod 3 == 0 || j' mod 5 == 0) ==> $hmap'[j'] == 0);
  {
    if (i' mod 3 == 0) {
      $hmap'[i'] := 1;
    }
    i' := i' + 1;
  }
  assert (forall j: int :: 0 <= j && j < n && !(j mod 3 == 0 || j mod 5 == 0) ==> $hmap[j] == 0);
  assert (forall j: int :: 0 <= j && j < n && (j mod 3 == 0 || j mod 5 == 0) ==> $hmap[j] == 1);
  assert (forall j: int :: 0 <= j && j < n && !(j mod 3 == 0 || j mod 5 == 0) ==> $hmap'[j] == 0);
  assert (forall j': int :: 0 <= j' && j' < n' && (j' mod 3 == 0 || j' mod 5 == 0) ==> $hmap'[j'] == 1);
  assert (forall i: int :: 0 <= i && i < n ==> $hmap[i] == $hmap'[i]);
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
