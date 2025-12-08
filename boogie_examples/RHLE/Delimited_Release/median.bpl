/*
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
*/

function precondition (a1_1, a2_1, b1_1, b2_1, a1_2, a2_2, b1_2, b2_2: int) returns (bool)
{
    (    // Low
        (a1_1 == a1_2) &&
        (a2_1 == a2_2) &&

        // Program Preconditions (ordered and distinct).
        (a1_1 < a2_1) &&
        (b1_1 < b2_1) &&
        (b1_2 < b2_2) &&

        (!(a1_1 == a2_1)) &&
        (!(a1_1 == b1_1)) &&
        (!(a1_1 == b2_1)) &&
        (!(a2_1 == b1_1)) &&
        (!(a2_1 == b2_1)) &&
        (!(b1_1 == b2_1)) &&

        (!(a1_2 == a2_2)) &&
        (!(a1_2 == b1_2)) &&
        (!(a1_2 == b2_2)) &&
        (!(a2_2 == b1_2)) &&
        (!(a2_2 == b2_2)) &&
        (!(b1_2 == b2_2)))
}
var m_1, m_2: int;

// verifies
procedure biprog (a1_1, a2_1, b1_1, b2_1, a1_2, a2_2, b1_2, b2_2: int) returns (ret_1, ret_2 : int)
  requires precondition(a1_1, a2_1, b1_1, b2_1, a1_2, a2_2, b1_2, b2_2);
  ensures ((m_1 == m_2) ==> (ret_1 == ret_2));  // Delimited Release
  modifies m_1, m_2;
{
   var x1_1, x1_2: int;
   var x2_1, x2_2: int;
   var a3_1, a3_2: int;
   var b3_1, b3_2: int;


   if (a1_1 <= b1_1)
      {x1_1 := 1;}
    else
      {x1_1 := 0;}
    
    if (x1_1 == 1)
      {a3_1 := a2_1;}
    else
      {a3_1 := a1_1;}
    

    if (x1_1 == 1) 
      {b3_1 := b1_1;}
    else
      {b3_1 := b2_1;}
    

    if (a3_1 <= b3_1)
      {x2_1 := 1;}
    else
      {x2_1 := 0;}


    if (x2_1 == 1)
      {m_1 := a3_1;}
    else
      {m_1 := b3_1;}

    ret_1 := m_1;

   if (a1_2 <= b1_2)
      {x1_2 := 1;}
    else
      {x1_2 := 0;}
    
    if (x1_2 == 1)
      {a3_2 := a2_2;}
    else
      {a3_2 := a1_2;}
    

    if (x1_2 == 1) 
      {b3_2 := b1_2;}
    else
      {b3_2 := b2_2;}
    

    if (a3_2 <= b3_2)
      {x2_2 := 1;}
    else
      {x2_2 := 0;}


    if (x2_2 == 1)
      {m_2 := a3_2;}
    else
      {m_2 := b3_2;}

    ret_2 := m_2;    

}    
