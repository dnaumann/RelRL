// From:
//   Rastogi, Aseem & Mardziel, Piotr & Hicks, Michael & Hammer, Matthew. (2013).
//   Knowledge inference for optimizing secure multi-party computation.
//   3-14. 10.1145/2465106.2465117.

expected: valid;

forall: median[1];
exists: median[2];

// High:
//   b1
//   b2
// Low:
//   a1
//   a2

// This example accomplishes delimited release by adding
// a predicate to the postcondition. Specifying a release
// in terms of a variable's *final* state can make the
// release easier to express, but has the disadvantage of
// obscuring the parts of the *initial* state that may be
// exposed.

pre: (and
       // Low
       (= median!1!a1 median!2!a1)
       (= median!1!a2 median!2!a2)

       // Program Preconditions (ordered and distinct).
       (< median!1!a1 median!1!a2)
       (< median!1!b1 median!1!b2)
       (< median!2!b1 median!2!b2)

       (not (= median!1!a1 median!1!a2))
       (not (= median!1!a1 median!1!b1))
       (not (= median!1!a1 median!1!b2))
       (not (= median!1!a2 median!1!b1))
       (not (= median!1!a2 median!1!b2))
       (not (= median!1!b1 median!1!b2))

       (not (= median!2!a1 median!2!a2))
       (not (= median!2!a1 median!2!b1))
       (not (= median!2!a1 median!2!b2))
       (not (= median!2!a2 median!2!b1))
       (not (= median!2!a2 median!2!b2))
       (not (= median!2!b1 median!2!b2)));

post: (=>
        // Delimited Release
        (= median!1!m median!2!m)

        (= median!1!ret median!2!ret));


fun median(a1, a2, b1, b2) {
  if (a1 <= b1) then
    x1 := 1;
  else
    x1 := 0;
  endif

  if (x1 == 1) then
    a3 := a2;
  else
    a3 := a1;
  endif

  if (x1 == 1) then
    b3 := b1;
  else
    b3 := b2;
       // Program Preconditions (or
  endif

  if (a3 <= b3) then
    x2 := 1;
  else
    x2 := 0;
  endif

  if (x2 == 1) then
    m := a3;
  else
    m := b3;
  endif

  ret := m;
  return ret;
}


procedure example (a1_1: int, a2_1: int, b1_1: int, b2_1: int) 
  returns (ret1: int, ret2: int, m1: int, m2: int)
    requires ()
    ensures ((m1 == m2) ==> ret1 == ret2)
{
    var a1_2: int; 
    var a2_2: int; 
    var b1_2: int; 
    var b2_2: int; 

    havoc a1_2;
    havoc a2_2;
    havoc b1_2;
    havoc b2_2;

    assume (// Low
            (a1_1 == a1_2) && 
            (a2_1 == a2_2) &&

            // Program Preconditions (ordered and distinct).
            (a1_1 < a2_1) &&
            (b1_1 < b2_1) &&
            (b1_2 < b2_2) &&

            (a1_1 != a2_1) &&
            (a1_1 != b1_1) &&
            (a1_1 != b2_1) &&
            (a2_1 != b1_1) &&
            (a2_1 != b2_1) &&
            (b1_1 != b2_1) &&

            (a1_2 != a2_2) && 
            (a1_2 != b1_2) && 
            (a1_2 != b2_2) && 
            (a2_2 != b1_2) && 
            (a2_2 != b2_2) && 
            (b1_2 != b2_2));

    
}
    
