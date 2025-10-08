// // From:
// //   Sabelfeld, Andrei & Myers, Andrew. (2004).
// //   A Model for Delimited Information Release.
// //   Lecture Notes in Computer Science. 10.1007/978-3-540-37621-7_9.

// expected: valid;

// forall: parity[1];
// exists: parity[2];

// // High:
// //   h
// // Low:
// //   l
// // Delimited Release:
// //   h mod 2

// pre: (and
//         (= parity!1!l parity!2!l)

//         // Delimited Release
//         (= (mod parity!1!h 2) (mod parity!2!h 2)));

// post: (= parity!1!l parity!2!l);


// fun parity() {
//   h := h % 2;
//   if (h == 1) then
//     l := 1;
//     h := 1;
//   else
//     l := 0;
//     h := 0;
//   endif
//   return 0;
// }

// verifies 

procedure example (l1: int, l2: int, h1: int, h2: int) returns (j1: int, j2: int)
    requires (l1 == l2 && (h1 mod 2) == (h2 mod 2));
    ensures (j1 == j2);
{
    var k1: int; var k2: int;
    j1 := l1; j2 := l2; 
    k1 := h1; k2 := h2;
    
    // h := h mod 2
    k1 := k1 mod 2;
    k2 := k2 mod 2;

    // if h == 1
    if (k1 == 1)
    {
        j1 := 1;
        k1 := 1;
    } else {
        j1 := 0;
        k1 := 0;
    }

    if (k2 == 1)
    {
        j2 := 1;
        k2 := 1;
    } else {
        j2 := 0;
        k2 := 0;
    }
}
