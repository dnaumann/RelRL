// [forall]
// int x;
// int c;
// int time; 
// int s;

// if * {
//     x = 0;
//     c = 0;
//     while (time > 0) {
//         time = time - 1;
//         x = x + 1;
//     }
// } else {
//     x = 0;
//     c = 1;
//     while (time > 0) {
//         time = time - 1;
//         s = *;
//         x = x + s;
//     }
// }

// [exists]
// int x;
// int c;
// int time; 
// int s;

// if * {
//     x = 0;
//     c = 0;
//     while (time > 0) {
//         time = time - 1;
//         x = x + 1;
//     }
// } else {
//     x = 0;
//     c = 1;
//     while (time > 0) {
//         time = time - 1;
//         s = *;
//         x = x + s;
//     }
// }

// [pre]
// time_0 == time_1

// [post]
// (c_0 == 0) => (c_1 == 1 && x_0 == x_1)


// Verifies.
// We added loop invariants and a precondition.  
// TODO should be valid without pre time1 >= 0 but doesn't verify

procedure example (time1: int, time2: int) returns (c1: int, c2: int, x1: int, x2: int)
    requires (time1 == time2);
    requires (time1 >= 0);  // added
    ensures (c1 == 0 ==> (c2 == 1 && x1 == x2));
{
    var k1: int; var k2: int;
    var s1: int;  var s2: int;
    var b1: bool; var b2: bool;
    k1 := time1; k2 := time2;

    havoc b1;
    if (b1)
    {
        x1 := 0;
        c1 := 0;
        while (k1 > 0)
           invariant (x1 + k1 == time1);
           invariant 0 <= k1;
        {
            k1 := k1 - 1;
            x1 := x1 + 1;
        }
    } else
    {
        x1 := 0;
        c1 := 1;
        while (k1 > 0)
        {
            k1 := k1 - 1;
            havoc s1;
            x1 := x1 + s1;
        }
    }
    assert (exists v:bool :: v != b1); // added by chk
    havoc b2;
    assume (b2 != b1);
    
    if (b2)
    {
        x2 := 0;
        c2 := 0;
        while (k2 > 0)
        {
            k2 := k2 - 1;
            x2 := x2 + 1;
        }
    } else
    {
        x2 := 0;
        c2 := 1;
        while (k2 > 0)
           invariant (x2 + k2 == time2);
           invariant 0 <= k2;
        {
            k2 := k2 - 1;
            assert (exists v:int :: v == 1); // added by chk 
            havoc s2;
            assume s2 == 1;
            x2 := x2 + s2;
        }
    }

}
