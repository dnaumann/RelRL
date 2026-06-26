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
