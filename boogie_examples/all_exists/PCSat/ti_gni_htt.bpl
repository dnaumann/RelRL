/* https://github.com/hiroshi-unno/coar/blob/299e979bfce7d9b0532586bfc42b449fd0451531/benchmarks/pfwnCSP/cav2021rel/TI_GNI_hTT.clp

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

specialized with high1 and high2
*/


procedure biprog (low1: int, low2: int) returns (x1: int, x2: int)
    requires low1 == low2;
    ensures x1 == x2;
{

    havoc x1;
    if (x1 >= low1)
    {
        x1 := x1;
    }
    else
    {
        x1 := low1;
    }


    assert ( exists v: int :: v == x1); // inserted by chk
    havoc x2;
    assume x2 == x1;

    if (x2 >= low2)
    {
        x2 := x2;
    }
    else
    {
        x2 := low2;
    }


}