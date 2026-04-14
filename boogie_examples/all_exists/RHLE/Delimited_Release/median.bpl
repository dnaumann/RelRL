/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/delimited-release/median-no-dr.imp
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
