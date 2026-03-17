/* demonstrates the difficulty of finding invariant 
   for Conditional_Loop using eager lockstep loop alignment */

procedure loop1 (x1: int, n1: int, x2: int, n2: int)
  returns (z1: int, z2: int)

  requires n1 > 0 && n2 > 0;
  requires x1 >= 0 && x2 >= 0;
  requires x1 == x2;
  ensures z1 == z2;
{

  var y1: int; var y2: int;
  var w1: int; var w2: int;

  y1 := x1; y2 := x2; 
  z1 := 0;  z2 := 0;  
  w1 := 0;  w2 := 0;  

  while (y1 > 0 && y2 > 0)
  {
       if (w1 == 0)
       { havoc z1; y1 := y1 - 1; }
       w1 := (w1 + 1) mod n1; 

       if (w2 == 0)
       { havoc z2; y2 := y2 - 1; }
       w2 := (w2 + 1) mod n2;         
  } 
  while (y1 > 0 && y2 <= 0)
  {
       if (w1 == 0)
       { havoc z1; y1 := y1 - 1; }
       w1 := (w1 + 1) mod n1; 
  } 
  while (y1 <= 0 && y2 > 0)
  {
       if (w2 == 0)
       { havoc z2; y2 := y2 - 1; }
       w2 := (w2 + 1) mod n2;         
  } 

}

