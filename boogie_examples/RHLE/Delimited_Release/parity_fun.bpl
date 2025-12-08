/*

// From:
//   Sabelfeld, Andrei & Myers, Andrew. (2004).
//   A Model for Delimited Information Release.
//   Lecture Notes in Computer Science. 10.1007/978-3-540-37621-7_9.

expected: valid;

forall: run[1];
exists: run[2];

// High:
//   h
// Low:
//   l
// Delimited Release:
//   h mod 2

pre: (and
        (= run!1!l run!2!l)

        // Delimited Release
        (= (mod run!1!h 2) (mod run!2!h 2)));

post: (= run!1!l run!2!l);

aspecs:
  parity(val) {
    pre: true;
    post: (= ret! (mod val 2));
  }

especs:
  parity(val) {
    pre: true;
    post: (= ret! (mod val 2));
  }

fun run() {
  p := parity(h);
  if (p == 1) then
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
