/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/delimited-release/parity.imp
*/

var l1, l2, h1, h2: int;

// verifies
procedure biprog() returns ()
  requires l1 == l2;
  requires h1 mod 2 == h2 mod 2; // delimited release
  modifies l1, l2, h1, h2;
  ensures l1 == l2;
{
  h1 := h1 mod 2;

  h2 := h2 mod 2;

  if (h1 == 1) 
  {
    l1 := 1;
    h1 := 1;
  }
  else
  {
    l1 := 0;
    h1 := 0;
  }

  if (h2 == 1) 
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
