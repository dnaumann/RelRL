/* https://github.com/hiroshi-unno/coar/blob/299e979bfce7d9b0532586bfc42b449fd0451531/benchmarks/pfwnCSP/cav2021rel/TS_GNI_hFF.clp

if (high) {
  x = *; // needs to depend on the return value of the other copy
  if (x >= low) { return x; } else { while (1) { } }
} else {
  x = low;
  while ( * ) { x++; }
  return x;
}

Copy 1 is scheduled demonically
Copy 2 is scheduled angelically

specialized with !high1 and !high2
*/

// same as ti_gni_hff.bpl

procedure biprog (low1: int, low2: int) returns (x1: int, x2: int)
    requires low1 == low2;
    ensures x1 == x2;
{
    var b1: bool; var b2: bool;

    x1 := low1; x2 := low2;

    havoc b1;

    assert ( exists v: bool :: v == b1 ); // inserted by chk
    havoc b2;
    assume b2 == b1;

    while (b1 || b2)
        invariant x1 == x2;
        invariant b1 <==> b2;
    {
        x1 := x1 + 1; x2 := x2 + 1;

        havoc b1;

        assert ( exists v: bool :: v == b1 ); // inserted by chk
        havoc b2;
        assume b2 == b1;


    }

}