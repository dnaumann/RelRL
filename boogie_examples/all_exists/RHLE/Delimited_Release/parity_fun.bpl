/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/delimited-release/parity-fun.imp
*/

var l1, l2, h1, h2: int;

// verifies
procedure biprog() returns ()
  requires l1 == l2;
  requires h1 mod 2 == h2 mod 2; // delimited release
  modifies l1, l2, h1, h2;
  ensures l1 == l2;
{
  var p1: int; var p2: int;

  // left prog calls with universal spec
  havoc p1; assume (h1 mod 2) ==  p1;

  assert (exists v: int :: v == p1);
  // right prog calls with existential spec
  havoc p2; assume (h2 mod 2) ==  p2;
  assume p2 == p1;

  if (p1 == 1) 
  {
    l1 := 1;
    h1 := 1;
  }
  else
  {
    l1 := 0;
    h1 := 0;
  }

  if (p2 == 1) 
  {
    l2 := 1;
    h2 := 1;
  }
  else
  {
    l2 := 0;
    h2 := 0;
  }

}
