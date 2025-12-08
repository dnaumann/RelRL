/* Simple example of data-dependent alignment. 
   Depends on havoc'd choices rather than input. */

procedure hiccupSum (n: int) returns (r: int)
{ var h: bool; var i: int;  
  i, r := 0, 0;
  havoc h;
  while (i < n) { 
    if (!h) { r := r+i; i := i+1; }
    havoc h;
  }   
} 
procedure hiccupSum_eq (n, n': int) returns (r, r': int)
  requires n == n';   ensures r == r';                     
{ 
  var h, h': bool; var i, i': int; 
  i, r := 0, 0;   i', r' := 0, 0;
  havoc h; havoc h';

  while (i < n || i' < n') // left/right alignment conditions h/h'
    invariant i == i';  
    invariant r == r'; 
    { 
      if (h && i < n) { // left body only 
        if (!h) { r := r+i; i := i+1; } havoc h;
      } else if (h' && i' < n') { // right body only 
        if (!h') { r' := r'+i'; i' := i'+1; } havoc h';
      } else if (i < n && i' < n' && !h && !h') { // both 
        if (!h) { r := r+i; i := i+1; } havoc h;
        if (!h') { r' := r'+i'; i' := i'+1; } havoc h';
      } else {
        assert false; // adequacy condition
      }       
   }
}

          
