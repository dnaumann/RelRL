/*
Version of reviewer's example where the unknown code c'
doesn't depend on initial value of low.

Two versions, both verify.
*/

function f(x: int): int;    

var x: int; 

procedure p () returns (res: int); // c' in the reviewer's code
          ensures res == f(old(x));  // unknown deterministic result 
          modifies x; 

/* alt version we played with
procedure p (x: int) returns (res: int);
          ensures res == f(x);  
*/

var x': int; 

procedure p' () returns (res: int);
          ensures res == f(old(x')); 
          modifies x'; 

procedure main () returns (low: int)
          modifies x;
{ 
  var d: bool; 
  d:=false;
  x:=0; call low := p(); havoc d;  // unroll 
  while (!d) 
    invariant low == f(0);
  { x:=0; call low := p(); havoc d; }
}

/* seql alignment to prove LMCS review example */

procedure main_NI () returns (low, low': int)
          ensures low==low';
          modifies x, x';
{ 
  var d,d': bool; 
  d, d' := false, false;
  // left copy of unrolled loop
  x:=0; call low := p(); havoc d;   // unroll 
  while (!d) 
    invariant low == f(0);
  { x:=0; call low := p(); havoc d; }
  // right copy of unrolled loop 
  x':=0; call low' := p'(); havoc d';  // unroll 
  while (!d') 
    invariant low == f(0);
    invariant low' == f(0);
  { x':=0; call low' := p'(); havoc d'; }
}

procedure main_NI_alt () returns (low, low': int)
          ensures low==low';
          modifies x, x';
{ 
  var d,d': bool; 
  d, d' := false, false;
  x:=0; call low := p(); havoc d;   // unroll 
  x':=0; call low' := p'(); havoc d';  // unroll 

  while (!d || !d') 
    // alignment conditions !d | !d'
    invariant low == f(0);
    invariant low' == f(0);
    invariant (!d || !d' || (!!d && !!d' && (!d <==> !d'))); // adequacy 
  { 
//    assert (!d || !d' || (!!d && !!d' && (!d && !d'))); // adequacy 
    if (!d)                            // left only
    { x:=0; call low := p(); havoc d; }
    else if (!d')                      // right only
    { x':=0; call low' := p'(); havoc d'; }
    else if (!d && !d' && !!d && !!d')    // joint (unreachable) 
    { x:=0; call low := p(); havoc d; 
      x':=0; call low' := p'(); havoc d'; }
  }
}

