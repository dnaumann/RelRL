method skip () returns ()
          modifies {}
{ }

method prog (high: int, low: int) returns (r: int)
 decreases *;
{
  var x: int; // could just use r, but trouble with loop specs?
  var b: int;
  if (high != 0) {
      x := *;
      if (x >= low) { 
         skip(); 
      } 
      else {
         while (true) 
            decreases *;
         { 
            skip(); 
         }
      }
  }
  else {
      x := low;
      b := *;
      while (b != 0) 
         decreases *
      {
          x := x+1;
          b := *;
      }
  }
  r := x;
}

function inst<a>(x: a) : bool { true }  

method Unno_possNI (high: int, low: int, high': int, low': int) returns (r: int, r':int)
          requires low == low'
          ensures r == r'
          decreases *
{ 
   var x, x': int;
   var b, b': int;
   var bsnap': int;
   var trigvar: int;

  if (high != 0 && high' != 0) 
  { 
   //   x := *; 
   //   assert (exists v {:trigger x} :: x == v); // inserted by chk
   //   x' := *; assume x == x'; // HavocR x { Agree x };
   //   if (x >= low || x' >= low') 
   //   { 
   //      skip();
   //   }
   //   else { 
   //      while (true) {  skip(); } 
   //      while (true) {  skip(); }
   //   }
  }
  else if (high != 0 && high' == 0) 
  { 
     x := *;
     if (x >= low) { skip(); } 
     else {  while (true) decreases * { skip(); }  }
      x' := low; 
      trigvar := x - x';
      assert inst(trigvar);
      assert (exists v:int {:trigger inst(v)}  ::  v == trigvar); // inserted by chk
      b' := *; assume b' == x - x'; // HavocR b
      while (b' != 0) 
         invariant b' >= 0
         invariant x >= x'
         invariant b' == x - x'
      {  
         bsnap' := b'; // variant b' inserted by chk
         x' := x' + 1; 
         trigvar := x - x';
         assert (exists v:int :: v == trigvar); // inserted by chk
         b' := *; assume b' == x - x'; // HavocR b
         assert b' < bsnap'; // variant decrease inserted by chk
      }
   }
   else if (high == 0 && high' != 0) { 
      x := low;
      b := *;
      while (b != 0)
         invariant x >= low
      { x := x+1; b := *; }
      assert (exists v:int :: x == v); // inserted by chk
      x' := *; assume x == x'; // HavocR x
      if (x' >= low) { skip(); }
      else {
         while (true) { skip(); } 
      }
    }
    else { // high == 0 && high' == 0;
       x := low; x' := low;
       b := *;
       assert (exists v:int :: b == v); // inserted by chk
       b' := *; assume b == b'; // HavocR b
       while (b != 0 || b' != 0) 
          invariant b == b' && x == x'
       { 
          x := x+1; x' := x'+1;
          b := *;
          assert (exists v:int :: b == v); // inserted by chk
          b' := *; assume b == b'; // HavocR b 
       }
    }
    r := x; r' := x';
}

// /* Alt version using trigger on some existentials,
//    and formatted compactly for use in slides.  */

// /* Hack to trigger instantiation. */
// function inst<a>(x: a) : bool { true }  

// method Unno_possNIalt (high: int, low: int, high': int, low': int) returns (x: int, x':int)
//           requires low == low';
//           ensures x == x'; 
// { var b, b': int;   
//   var bsnap': int; // added by chk

//   if (high != 0 && high' != 0) { 
//      x := *; 
//      assert (exists v:int :: x == v); // added by chk
//      x' := *; assume x == x';  
//      if (x >= low || x' >= low') { /*skip*/ }
//      else { while (true) { /*skip*/ } }
//   }
//   else if (high != 0 && high' == 0) { 
//      x := *;
//      if (x >= low) { /*skip*/ } 
//      else { while (true) { /*skip*/ } }
//       x' := low; 
//       assert inst(x - x');
//       assert exists v:: v == x - x'; // added by chk
//       b' := *; assume b' == x - x'; 
//       while (b' != 0) 
//          invariant x >= x' && b' == x - x' /* variant b' */
//       {  bsnap' := b'; // added by chk
//          x' := x' + 1; 
//          assert inst(x - x');
//          assert (exists v:: v == x - x'); // added by chk
//          b' := *; assume b' == x - x'; 
//          assert b' < bsnap'; // added by chk
//       }
//    }
//    else if (high == 0 && high' != 0) { 
//       x := low; 
//       b := *;
//       while (b != 0)
//          invariant x >= low
//       { x := x+1; b := *; }
//       assert (exists v:int :: x == v); // added by chk
//       x' := *; assume x == x'; 
//       if (x' >= low) { /*skip*/ }
//       else { while (true) { /*skip*/ } }
//     }
//     else { // high == 0 && high' == 0;
//        x := low; x' := low;
//        b := *;
//        assert (exists v:int :: b == v); // added by chk
//        b' := *; assume b == b'; 
//        while (b != 0 || b' != 0) 
//           invariant b == b' && x == x'
//        {  x := x+1; x' := x'+1;
//           b := *;
//           assert (exists v:int :: b == v); // added by chk
//           b' := *; assume b == b'; 
//        }
//     }
// }

