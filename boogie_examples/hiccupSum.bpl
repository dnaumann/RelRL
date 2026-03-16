/* Simple example of data-dependent alignment. 
   Depends on havoc'd choices rather than input. 
   Could verify with lockstep but then it's not an example of data dependent.
*/

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

  while (i < n || i' < n') // left/right alignment conditions h and (!h && h')
    invariant i == i';  
    invariant r == r';
    invariant (i < n && i' < n') || (i >= n && i' >= n') || (i < n && h) || (i' < n' && (!h && h'));
    { 
      if (h && i < n) { // left only 
        if (!h) { r := r+i; i := i+1; } havoc h;
      } else if (!h && h' && i' < n') { // right only 
        if (!h') { r' := r'+i'; i' := i'+1; } havoc h'; assume !h'; 
      } else if (i < n && i' < n' && !h && !(!h && h')) { // both 
        if (!h) { r := r+i; i := i+1; } havoc h;
        if (!h') { r' := r'+i'; i' := i'+1; } havoc h'; // no need for filter?
      } else {
        assert false; // adequacy condition
      }       
   }
}

function bool2int(x:bool):int { if x then 1 else 0 } 

procedure hiccupSum_eq_chk (n, n': int) returns (r, r': int)
  requires n == n';   ensures r == r';                     
{ 
  var h, h': bool; var i, i': int; 
  var vsnap: int; var rosnap: bool;
  i, r := 0, 0;   i', r' := 0, 0;
  havoc h; havoc h';

  while (i < n || i' < n') // left/right alignment conditions h and (!h && h')
    invariant i == i';    // variant: bool2int(h')
    invariant r == r';
    invariant (i < n && i' < n') || (i >= n && i' >= n') || (i < n && h) || (i' < n' && (!h && h'));
    { 
      vsnap := bool2int(h'); // added by chk
      rosnap := i' < n' && !h && h'; // added by chk 
      if (h && i < n) { // left only 
        if (!h) { r := r+i; i := i+1; } havoc h;
      } else if (!h && h' && i' < n') { // right only 
        if (!h') { r' := r'+i'; i' := i'+1; } 
        assert (exists v:bool :: v == !h'); // added by chk
        havoc h'; assume (!h'); 
      } else if (i < n && i' < n' && !h && !(!h && h')) { // both 
        if (!h) { r := r+i; i := i+1; } havoc h;
        if (!h') { r' := r'+i'; i' := i'+1; } 
        havoc h'; // no filter needed 
      } else {
        assert false; // adequacy condition
      }       
      assert rosnap ==> 0 <= bool2int(h');
      assert rosnap ==> bool2int(h') < vsnap;
   }
}
          
