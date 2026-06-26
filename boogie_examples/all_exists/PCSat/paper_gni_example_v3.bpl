procedure skip () returns ()
          modifies ;
{ }

/* Alt version using trigger variable scheme,
   and formatted compactly for use in slides.  */

procedure Unno_possNI (high: int, low: int, high': int, low': int) returns (r: int, r':int)
          requires low == low';
          ensures r == r'; 
{ var x, x': int;
  var b, b': int;
  var bsnap': int;
  var trigvar: int;

  if (high != 0 && high' != 0) { 
     havoc x; 
     assert (exists v:int :: x == v); // inserted by chk
     havoc x';
     assume x == x'; // HavocR x { Agree x };
     if (x >= low || x' >= low') { 
        call skip();
     }
     else { 
        while (true) { call skip(); } 
        while (true) { call skip(); }
     }
  }
  else if (high != 0 && high' == 0) { 
     havoc x;
     if (x >= low) { call skip(); } 
     else {  while (true) { call skip(); }  }
      x' := low; 
      trigvar := x - x';
      assert (exists v:int :: v == trigvar); // inserted by chk
      havoc b';
      assume b' == x - x'; // HavocR b
      while (b' != 0) 
         invariant b' >= 0;
         invariant x >= x';
         invariant b' == x - x';
      {  
         bsnap' := b'; // variant b' inserted by chk
         x' := x' + 1; 
         trigvar := x - x';
         assert (exists v:int :: v == trigvar); // inserted by chk
         havoc b';
         assume b' == x - x'; // HavocR b
         assert (0 <= b' && b' < bsnap'); // variant decrease inserted by chk
      }
   }
   else if (high == 0 && high' != 0) { 
      x := low;
      havoc b;
      while (b != 0)
         invariant x >= low;
      { x := x+1;
      havoc b; }
      assert (exists v:int :: x == v); // inserted by chk
      havoc x';
      assume x == x'; // HavocR x
      if (x' >= low) { call skip(); }
      else {
         while (true) { call skip(); } 
      }
    }
    else { // high == 0 && high' == 0;
       x := low; x' := low;
       havoc b;
       assert (exists v:int :: b == v); // inserted by chk
       havoc b';
       assume b == b'; // HavocR b
       while (b != 0 || b' != 0) 
          invariant b == b' && x == x';
       { 
          x := x+1; x' := x'+1;
          havoc b;
          assert (exists v:int :: b == v); // inserted by chk
          havoc b';
          assume b == b'; // HavocR b 
       }
    }
    r := x; r' := x';
}

