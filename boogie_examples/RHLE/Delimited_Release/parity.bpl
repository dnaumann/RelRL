/*
// From:
//   Sabelfeld, Andrei & Myers, Andrew. (2004).
//   A Model for Delimited Information Release.
//   Lecture Notes in Computer Science. 10.1007/978-3-540-37621-7_9.

expected: valid;

forall: parity[1];
exists: parity[2];

// High:
//   h
// Low:
//   l
// Delimited Release:
//   h mod 2

pre: (and
        (= parity!1!l parity!2!l)

        // Delimited Release
        (= (mod parity!1!h 2) (mod parity!2!h 2)));

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
