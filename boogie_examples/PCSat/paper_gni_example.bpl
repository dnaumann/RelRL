  /* Example from Unno'21: Constraint-based relational verification */

procedure skip () returns ()
          modifies ;
{ }

procedure Unno (high: int, low: int) returns (r: int)
{
  var x: int; // could just use r, but trouble with loop specs?
  var b: int;
  if (high != 0) {
      havoc x;
      if (x >= low) { 
         call skip(); 
      } 
      else {
         while (true) { 
            call skip(); 
         }
      }
  }
  else {
      x := low;
      havoc b;
      while (b != 0) {
          x := x+1;
          havoc b;
      }
  }
  r := x;
}

procedure Unno_possNI (high: int, low: int, high': int, low': int) returns (r: int, r':int)
          requires low == low';
          ensures r == r'; 
{ var x, x': int;
  var b, b': int;
  var bsnap': int;

  if (high != 0 && high' != 0) { 
     havoc x; 
     havoc x'; assume x == x'; // HavocR x { Agree x };
     if (x >= low || x' >= low') { 
        call skip();
     }
     else { 
//        ( while true do skip done | skip );
        while (true) { call skip(); } 
        assert false; // added by user 
//        ( skip | while true do variant { 0 } skip done );
        while (true) { call skip(); }
     }

    assert x == x'; 
  }

  else if (high != 0 && high' == 0) { 
     havoc x;
     if (x >= low) { call skip(); } 
     else {  while (true) { call skip(); }  }
   //      Assert { <| x >= low <] };
      assert x >= low; 
      x' := low; 
   //      HavocR b { [> b >] = [< x <] - [> x >] };
      havoc b'; assume b' == x - x';
   //      WhileR b <> 0 do
      while (b' != 0) 
   //         invariant { [> b >= 0 |> }
         invariant b' >= 0;
   //         invariant { [< x <] >= [> x >] }
         invariant x >= x';
   //         invariant { [> b >] = [< x <] - [> x >] }
         invariant b' == x - x';
   //         variant { [> b >] }
      {  
         bsnap' := b'; // variant b'
         x' := x' + 1; 
   //        HavocR b { [> b >] = [< x <] - [> x >] }
         havoc b'; assume b' == x - x';
         assert 0 <= b' && b' < bsnap'; // variant decrease
      }

    assert x == x'; 
   }
   else if (high == 0 && high' != 0) { 
//       ( x := low; havoc b | skip );
      x := low;
      havoc b;
//      WhileL b <> 0 do
      while (b != 0)
         invariant x >= low;
      { x := x+1; havoc b; }
//      HavocR x { Agree x };
      havoc x'; assume x == x'; 
      if (x' >= low) { call skip(); }
      else {
         assert false; // added by user
         while (true) { call skip(); } 
      }
    assert x == x'; 
    }
    else { 
       assert high == 0 && high' == 0;
       x := low; x' := low;
//      ( havoc b | skip ); HavocR b { Agree b };
       havoc b;
       havoc b'; assume b == b';
//      While b <> 0 | b <> 0 . do
       while (b != 0 || b' != 0) 
          invariant b == b' && x == x';
       { 
          x := x+1; x' := x'+1;
          havoc b;
//      HavocR b { Agree b };
          havoc b'; assume b == b';
       }
    assert x == x'; 

    }
    assert x == x'; 
    r := x; r' := x';
}
