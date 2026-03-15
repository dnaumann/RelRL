/*

// From:
//   Sabelfeld, Andrei & Myers, Andrew. (2004).
//   A Model for Delimited Information Release.
//   Lecture Notes in Computer Science. 10.1007/978-3-540-37621-7_9.

expected: invalid;

forall: parity[1];
exists: parity[2];

// High:
//   h
// Low:
//   l

pre:  (= parity!1!l parity!2!l);
post: (= parity!1!l parity!2!l);


fun parity() {
  h := h % 2;
  if (h == 1) then
    l := 1;
    h := 1;
  else
    l := 0;
    h := 0;
  endif
  return 0;
}

*/

var l1, l2, h1, h2: int;

// should not and does not verify
procedure biprog() returns ()
  requires l1 == l2;
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
