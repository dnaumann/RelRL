/* Code from https://github.com/ravenbeutner/ForEx/blob/main/benchmarks/hypa/compiler_opt.txt */

// [forall]
// int o;
// int x;

// o = 0;
// while (x > 0) {
//     x = x - 1;
//     if * {
//         o = o + 1;
//     } else {
//         skip;
//     }
// }

// [exists]
// int o;
// int x;
// int s;

// o = 0;
// while (x > 0) {
//     x = x - 1;
//     s = *;
//     o = o + s;
// }

// [pre]
// x_0 == x_1

// [post]
// o_0 == o_1


procedure example (n1: int, n2: int) returns (o1: int, o2: int)
          requires n1 == n2;
          ensures  o1 == o2;
{
  var x1: int; var x2: int;
  var g1: int; // ghost
  var b1: bool;
  var s2: int;

  x1 := n1; x2 := n2;
  o1 := 0; o2 := 0;

  while (x1 > 0 || x2 > 0)
        invariant x1 == x2;
        invariant o1 == o2;
        // adequacy
        invariant (x1 > 0) <==> (x2 > 0);
  {
    x1 := x1 - 1; x2 := x2 - 1;

    havoc b1;
    if (b1)
    {
        o1 := o1 + 1;
    }

    // Jude's trick: have to use a ghost variable
    // The assertion below (exists v :: v == o1 - o2)
    // doesn't verify in Boogie for some reason...
    g1 := o1 - o2;

    // assert (exists v: int :: v == o1 - o2); // fails
    assert (exists v: int :: v == g1);

    havoc s2;
    assume s2 == g1;

    o2 := o2 + s2;
  }
}

