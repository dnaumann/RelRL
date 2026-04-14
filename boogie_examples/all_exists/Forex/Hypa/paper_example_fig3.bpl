// https://github.com/ravenbeutner/ForEx/blob/main/benchmarks/hypa/paper_example_fig3.txt
// verifies

procedure example(a1: int, a2: int) returns (y1: int, y2: int)
    requires (a1 == a2);
    ensures (y1 == y2);
{
    var k1: int; var k2: int;
    var x1: int; var x2: int;
    var t1: bool;

    k1 := a1; k2 := a2;
    
    havoc x1;
    havoc t1;

    while (t1)
    {
        havoc t1;
        x1 := x1 + 1;
    }

    assert (exists v: int :: v == x1);
    havoc x2;
    assume (x1 == x2);

    y1 := x1;
    y2 := x2;

    while (y1 > 0 && y2 > 0)
      invariant (y1 == y2);
    {
        y1 := y1 - 1;
        y2 := y2 - 1;
        k1 := k1 + x1;
        k2 := k2 + x2;
    }

}