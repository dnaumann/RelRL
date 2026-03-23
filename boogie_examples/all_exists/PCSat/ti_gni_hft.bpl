/* https://github.com/hiroshi-unno/coar/blob/299e979bfce7d9b0532586bfc42b449fd0451531/benchmarks/pfwnCSP/cav2021rel/TI_GNI_hFT.clp

if (high) {
  x = *; // needs to depend on the return value of the other copy
  if (x >= low) { return x; } else { return low; }
} else {
  x = low;
  while ( * ) { x++; }
  return x;
}

Copy 1 is scheduled demonically
Copy 2 is scheduled angelically

specialized with !high1 and high2
*/


procedure biprog (l1: int, l2: int) returns (x1: int, x2: int)
    requires l1 == l2;
    ensures x1 == x2;
{
    var a1: bool; var a2: bool;

    x1 := l1; 
    havoc a1;
    while (a1)
      invariant x1 >= l1;
    {
        x1 := x1 + 1;
        havoc a1;
    }


    assert ( exists v: int :: v == x1); // inserted by chk
    havoc x2;
    assume x2 == x1;

    if (x2 <= l2)
    {
        x2 := l2;
    }
    else
    {
        x2 := x2;
    }

}