procedure fact (x: int) returns (z: int)   
{ var y: int; y := 0; z := 1;
  while (y < x) { y := y+1; z := z*y; } } 

procedure fact' (x: int) returns (z: int)
{ var y: int; y := 1; z := 1;
  while (y <= x) { z := z*y; y := y+1; } }

procedure fact_eq (x, x': int) returns (z, z': int)
  requires x == x' && x >= 0;    ensures z == z';                     
{ var y, y': int; 
  y := 0; y' := 1; z := 1; z' := 1; 
  while (y < x) 
    invariant y' == y + 1 && 0 <= y && y <= x;
    invariant z == z' && z > 0; 
    invariant y < x <==> y' <= x; // adequacy
    { y := y+1; z := z * y; z' := z' * y'; y' := y'+1; }
}


/* equivalence example from Shemer et al ATVA'23. */

procedure dblsq (x: int) returns (r: int)
  requires x >= 0; ensures r == 2 * x * x;
{ var z: int; 
  r := 0; z := 2 * x; 
  while (z > 0)
    invariant 0 <= z && z <= 2*x && r == x*(2*x - z);
  { z := z-1; r := r+x; }
}

procedure dblsq' (x: int) returns (r: int)
  requires x >= 0; ensures r == 2 * x * x;
{ var z: int; 
  r := 0; z := x; 
  while (z > 0)
    invariant 0 <= z && z <= x && r == x*(x-z);
  { z := z-1; r := r+x; }
  r := 2*r;
}

procedure dblsq_eq (x, x': int) returns (r, r': int)
  requires x == x' && x >= 0; ensures r == r'; 
{ var z, z': int; 
  r := 0; z := 2*x; 
  r' := 0; z' := x;
  while (z > 0 || z' > 0)
    invariant z == 2*z' && r == 2*r' && z' >= 0; 
      { z := z-1; r := r+x; 
        if (z > 0) { z := z-1; r := r+x; }
        z' := z'-1; r' := r'+x';
  }
  r' := 2*r';
}




          
