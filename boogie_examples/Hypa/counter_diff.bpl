// [forall]
// int a;
// int x;
// int t;

// a = 0;
// x = *;
// while (t > 0) {
//     t = t - 1;
//     a = a + x;
// }

// [exists]
// int a;
// int x;
// int t;

// a = 0;
// x = *;
// while (t > 0) {
//     t = t - 1;
//     a = a + x;
// }

// [pre]
// t_0 == t_1

// [post]
// a_0 == -a_1

procedure counter_diff(t1: int, t2: int) returns (a1: int, a2: int)
    requires (t1 == t2);
    ensures (a1 == -a2);
{
    var k1: int; var k2: int;
    var x1: int; var x2: int;
    var g: int;
    
    k1 := t1; k2 := t2;
    a1 := 0; a2 := 0;
    
    havoc x1;
    g := -x1;
    assert (exists v: int :: v == g);
    havoc x2;

    assume x2 == -x1;

    while(k1 > 0 && k2 > 0)
        invariant a1 == -a2;
    {
        k1 := k1 - 1;
        k2 := k2 - 1;
        a1 := a1 + x1;
        a2 := a2 + x2;
    }
}
