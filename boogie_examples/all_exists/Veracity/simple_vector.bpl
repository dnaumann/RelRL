// https://github.com/veracity-lang/veracity2g/blob/main/benchmarks/global_commutativity/simple-vector.vcy


var x, x': [int]int;
var y, y': [int]int;
var z, z': [int]int;

procedure main() returns (ret: int)
  modifies x, y, z;
{
  var l, i, j, k, sum, rand_val: int;

  sum := 0;
  l := 0;
  i := 0;
  j := 0;
  k := 0;

  while (l < 1000)
    invariant 0 <= l && l <= 1000;
  {
    havoc rand_val;
    assume -256 <= rand_val && rand_val <= 256;
    
    x[l] := rand_val;
    if (l == 999) 
    {
      x[l] := 1;
    }
    
    l := l + 1;
  }

  // f1
  while (i < 1000)
    invariant 0 <= i && i <= 1000;
  {
    y[i] := x[i] * x[i];
    
    i := i + 1;
  }

  while (j < 1000)
    invariant 0 <= j && j <= 1000;
  {
    sum := sum + y[j];
    
    j := j + 1;
  }

  // f2
  while (k < 1000)
    invariant 0 <= k && k <= 1000;
  {
    z[k] := x[999 - k];
    
    k := k + 1;
  }

  ret := z[0];
  return;
}

procedure commutativity_check()
  modifies y, z, y', z';
{
  var i, i': int;
  var k, k': int;
  var vsnap: int;

  // assume x = x'
  assume (forall m: int :: x[m] == x'[m]);

  // f1; f2 

  i := 0;
  while (i < 1000)
    invariant 0 <= i && i <= 1000;
    invariant (forall m: int :: 0 <= m && m < i ==> y[m] == x[m] * x[m]);
  {
    y[i] := x[i] * x[i];
    i := i + 1;
  }

  k := 0;
  while (k < 1000)
    invariant 0 <= k && k <= 1000;
    invariant (forall m: int :: 0 <= m && m < k ==> z[m] == x[999 - m]);
    invariant (forall m: int :: 0 <= m && m < 1000 ==> y[m] == x[m] * x[m]);
  {
    z[k] := x[999 - k];
    k := k + 1;
  }

  // f2; f1

  k' := 0;
  while (k' < 1000)
    invariant 0 <= k' && k' <= 1000;
    invariant (forall m: int :: 0 <= m && m < k' ==> z'[m] == x'[999 - m]);
  {
    vsnap := 1000 - k'; // variant

    z'[k'] := x'[999 - k'];
    k' := k' + 1;

    assert (0 <= 1000 - k' && 1000 - k' < vsnap); // variant decreases
  }

  i' := 0;
  while (i' < 1000)
    invariant 0 <= i' && i' <= 1000;
    invariant (forall m: int :: 0 <= m && m < i' ==> y'[m] == x'[m] * x'[m]);
    invariant (forall m: int :: 0 <= m && m < 1000 ==> z'[m] == x'[999 - m]);
  {
    vsnap := 1000 - i'; // variant

    y'[i'] := x'[i'] * x'[i'];
    i' := i' + 1;

    assert (0 <= 1000 - i' && 1000 - i' < vsnap); // variant decreases
  }

  // check y equals y' and z equals z'
  assert (forall m : int :: 0 <= m && m < 1000 ==> y[m] == y'[m] && z[m] == z'[m]);
  
}


procedure commutativity_check_lockstep()
  modifies y, z, y', z';
{
  var i, i': int;
  var k, k': int;
  var vsnap: int;

  // assume x = x'
  assume (forall m: int :: x[m] == x'[m]);

  // (f1 | skip)  

  i := 0;
  while (i < 1000)
    invariant 0 <= i && i <= 1000;
    invariant (forall m: int :: 0 <= m && m < i ==> y[m] == x[m] * x[m]);
  {
    y[i] := x[i] * x[i];
    i := i + 1;
  }


  // (f2 | f2)
  k := 0;  k' := 0;
  while (k < 1000 && k' < 1000)
    invariant k == k';
    invariant (forall m: int :: 0 <= m && m < k ==> z[m] == x[999 - m]);
    invariant (forall m: int :: 0 <= m && m < k' ==> z'[m] == x'[999 - m]);
    invariant (forall m: int :: 0 <= m && m < 1000 ==> y[m] == x[m] * x[m]);
    invariant (k < 1000 && k' < 1000) || (k >= 1000 && k' >= 1000); // lockstep
  {
    vsnap := 1000 - k'; // variant

    z[k] := x[999 - k]; z'[k'] := x'[999 - k'];
    k := k + 1; k' := k' + 1;

    assert (0 <= 1000 - k' && 1000 - k' < vsnap); // variant decreases
  }

  // skip | f1

  i' := 0;
  while (i' < 1000)
    invariant 0 <= i' && i' <= 1000;
    invariant (forall m: int :: 0 <= m && m < i' ==> y'[m] == x'[m] * x'[m]);
    invariant (forall m: int :: 0 <= m && m < 1000 ==> z'[m] == x'[999 - m]);
  {
    vsnap := 1000 - i'; // variant

    y'[i'] := x'[i'] * x'[i'];
    i' := i' + 1;

    assert (0 <= 1000 - i' && 1000 - i' < vsnap); // variant decreases
  }

  // check y equals y' and z equals z'
  assert (forall m : int :: 0 <= m && m < 1000 ==> y[m] == y'[m] && z[m] == z'[m]);
  
}