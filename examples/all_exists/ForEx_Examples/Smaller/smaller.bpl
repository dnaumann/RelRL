// [forall]
// int x;
// int time; 

// x = 0;
// while (time > 0) {
//     time = time - 1;
//     if * {
//         x = x + 1;
//     } else {
//         x = x + 3;
//     }
// }


// [exists]
// int x;
// int time; 

// x = 0;
// while (time > 0) {
//     time = time - 1;
//     if * {
//         x = x + 1;
//     } else {
//         x = x + 3;
//     }
// }

// [pre]
// time_0 == time_1

// [post]
// x_1 <= x_0

procedure example (time1: int, time2: int) returns (x1: int, x2: int)
    requires (time1 == time2);
    ensures (x2 <= x1);
{
    var k1: int; var k2: int;
    var b1: bool; var b2: bool;

    k1 := time1; k2 := time2;

    x1 := 0; x2 := 0;

    while (k1 > 0 && k2 > 0)
     invariant (x2 <= x1);
    {
        k1 := k1 - 1;
        k2 := k2 - 1;
        havoc b1;

        if (b1)
        {
            x1 := x1 + 1;
        } else
        {
            x1 := x1 + 3;
        }

        assert (exists v: bool :: v == b1);
        havoc b2;
        assume (b1 == b2);

        if (b2)
        {
            x2 := x2 + 1;
        } else
        {
            x2 := x2 + 3;
        }

    } 
}