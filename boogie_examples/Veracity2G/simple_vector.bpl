// https://github.com/veracity-lang/veracity2g/blob/main/benchmarks/global_commutativity/simple-vector.vcy

// commutativity {
//     {f1}, {f2}: (true)
// }

// int[] x = new int[1000];
// int[] y = new int[1000];
// int[] z = new int[1000];
// int sum = 0;
// int l = 0;
// int i = 0;
// int j = 0;
// int k = 0;
// /*string[] argv = new string[5];*/

// int main(int argc, string[] argv) {
//     int scalingfactor = int_of_string(argv[1]);

//     while(l < 1000) {
//         x[l] = random(-256, 256);
//         if(l == 999) {x[l] = 1;}
//         l = l + 1;
//     }

//     f1:{ 
//         while(i < 1000) {
//             y[i] = x[i] * x[i];
//             i = i + 1;
//             busy_wait(scalingfactor);
//         }
//     }
    
//     while(j < 1000) {
//         sum = sum + y[j];
//         j = j + 1;
//         /* busy_wait(scalingfactor); */
//     }

//     f2:{ 
//         while(k < 1000) {
//             z[k] = x[999-k];
//             k = k + 1;
//             busy_wait(scalingfactor);
//         }
//     }
    
//     return z[0];
// }
    

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
    z'[k'] := x'[999 - k'];
    k' := k' + 1;
  }

  i' := 0;
  while (i' < 1000)
    invariant 0 <= i' && i' <= 1000;
    invariant (forall m: int :: 0 <= m && m < i' ==> y'[m] == x'[m] * x'[m]);
    invariant (forall m: int :: 0 <= m && m < 1000 ==> z'[m] == x'[999 - m]);
  {
    y'[i'] := x'[i'] * x'[i'];
    i' := i' + 1;
  }

  // check y equals y' and z equals z'
  assert (forall m : int :: 0 <= m && m < 1000 ==> y[m] == y'[m] && z[m] == z'[m]);
  
}
