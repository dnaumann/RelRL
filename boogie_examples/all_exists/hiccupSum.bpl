/* Simple example of data-dependent alignment. This can be verified using 
   lockstep alignment and havoc-filter.  Instead we use data-dependent 
   alignment for the sake of a very simple example of that.
*/

function bool2int(x:bool):int { if x then 1 else 0 } 

procedure hiccupSum (n: int) returns (r: int)
{ var h: bool; var i: int;  
  i, r := 0, 0;
  havoc h;
  while (i < n) { 
    if (!h) { r := r+i; i := i+1; }
    havoc h;
  }   
} 

// the user-provided product to show hiccupSum refines itself 
procedure hiccupSum_ref (n, n': int) returns (r, r': int)
  requires n == n';   ensures r == r';                     
{ 
  var h, h': bool; var i, i': int; 
  i, r := 0, 0;   i', r' := 0, 0;   // lockstep alignment
  havoc h;       havoc h';      

  while (i < n || i' < n') // left alignment condition: h
                           // right alignment condition: !h && h'
                           // variant: bool2int(h') 
    invariant i == i';  
    invariant r == r';
    invariant (i < n && i' < n') || (i >= n && i' >= n') // adequacy
            || (i < n && h) || (i' < n' && (!h && h'));
    { 
      if (i < n && h) { // left only 
          if (!h) { r := r+i; i := i+1; } 
          havoc h;
      } else if (i' < n' && !h && h') { // right only 
          if (!h') { r' := r'+i'; i' := i'+1; } 
          havoc h'; assume !h'; // havoc-filter
      } else { 
          assert (i < n && i' < n' && !h && !(!h && h')); // just a remark; from adequacy
          if (!h) { r := r+i; i := i+1; }    // sequential alignment 
          havoc h;
          if (!h') { r' := r'+i'; i' := i'+1; } 
          havoc h'; // no need for filter in this example 
      } 
    }
}

// transformed from the user-provided product 
procedure hiccupSum_ref_chk (n, n': int) returns (r, r': int)
  requires n == n';   ensures r == r';                     
{ 
  var h, h': bool; var i, i': int;   var vsnap: int; var rosnap: bool;
  i, r := 0, 0;   i', r' := 0, 0;
  havoc h; havoc h';

  while (i < n || i' < n') 
    invariant i == i';  
    invariant r == r';
    invariant (i < n && i' < n') || (i >= n && i' >= n')
            || (i < n && h) || (i' < n' && (!h && h'));
    { 
      vsnap := bool2int(h');             // added by chk
      rosnap := i' < n' && !h && h';    // added by chk 
      if (i < n && h) {                
          if (!h) { r := r+i; i := i+1; } 
          havoc h;
      } else if (i' < n' && !h && h') {  
          if (!h') { r' := r'+i'; i' := i'+1; } 
          assert (exists v:bool :: v == !h');  // added by chk
          havoc h'; assume !h';        
      } else { 
          if (!h) { r := r+i; i := i+1; } 
          havoc h;
          if (!h') { r' := r'+i'; i' := i'+1; } 
          havoc h'; 
      } 
      assert rosnap ==> 0 <= bool2int(h');     // added by chk
      assert rosnap ==> bool2int(h') < vsnap; // added by chk
    }
}
          
/*  Note that if one replaces the right-only alignment condition 
    by simply h', which isn't mutually exclusive with respect to
    the left-only condition, then the variant-decrease assertion 
    inserted by chk fails because it doesn't hold on left-only paths.
*/
