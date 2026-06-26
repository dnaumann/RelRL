  /* Example from Unno'21: Constraint-based relational verification */

procedure skip () returns ()
          modifies ;
{ }


/* Hack to trigger instantiation. */
function inst<a>(x: a) : bool { true }  

procedure Unno_possNIalt (high: int, low: int, high': int, low': int) returns (x: int, x':int)
          requires low == low';
          ensures x == x'; 
{ var b, b': int;   
  var bsnap': int; // added by chk

  if (high != 0 && high' != 0) { 
     havoc x; 
     assert (exists v:int :: x == v); // added by chk
     havoc x';
     assume x == x';  
     if (x >= low || x' >= low') { /*skip*/ }
     else { while (true) { /*skip*/ } }
  }
  else if (high != 0 && high' == 0) { 
     havoc x;
     if (x >= low) { /*skip*/ } 
     else { while (true) { /*skip*/ } }
      x' := low; 
      assert inst(x - x');
      assert (exists v:int :: {inst(v)} v == x - x'); // added by chk
      havoc b';
      assume b' == x - x'; 
      while (b' != 0) 
         invariant x >= x' && b' == x - x'; /* variant b' */
      {  bsnap' := b'; // added by chk
         x' := x' + 1; 
         assert inst(x - x');
         assert (exists v:int :: {inst(v)} v == x - x'); // added by chk
         havoc b';
         assume b' == x - x'; 
         assert (0 <= b' && b' < bsnap'); // added by chk
      }
   }
   else if (high == 0 && high' != 0) { 
      x := low; 
      havoc b;
      while (b != 0)
         invariant x >= low;
      { x := x+1;
      havoc b; }
      assert (exists v:int :: x == v); // added by chk
      havoc x';
      assume x == x'; 
      if (x' >= low) { /*skip*/ }
      else { while (true) { /*skip*/ } }
    }
    else { // high == 0 && high' == 0;
       x := low; x' := low;
       havoc b;
       assert (exists v:int :: b == v); // added by chk
       havoc b';
       assume b == b'; 
       while (b != 0 || b' != 0) 
          invariant b == b' && x == x';
       {  x := x+1; x' := x'+1;
          havoc b;
          assert (exists v:int :: b == v); // added by chk
          havoc b';
          assume b == b'; 
       }
    }
}

