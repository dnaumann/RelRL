// ALL-EXISTS examples done in Boogie
//
// To run: boogie <filename>.bpl
//
// See https://github.com/boogie-org/boogie for instructions
// on how to install Boogie
//
// For emacs support, install
// https://github.com/boogie-org/boogie-friends


// Example 1
// havoc x | havoc x : true =e=> Agr x

// globals
var x.L: int;
var x.R: int;

// testing is the product program corresponding
// to the chk(B) where B is the biprogram:
//   ( havoc x | skip );
//   havocF x { x =:= x };
// Left and right projections of B match the original programs.

procedure testing () returns ()
  ensures x.L == x.R;
  modifies x.L, x.R;
{
  havoc x.L;

  assert (exists v: int :: x.L == v); // added by chk

  havoc x.R;
  assume x.L == x.R;
}

procedure client () returns ()
  ensures x.L == x.R;
  modifies x.L, x.R;
{
  call testing();
}


/*
Example 2: conditionally aligned loops

Note that this example cannot be done in ForEx (Beutner'24) or in RHLE
(Dickerson'22).  Those tools don't handle conditionally aligned loops.
Can this be done in Hyper Hoare logic?  Probably not, because they
don't support dissonant loops.

  meth m (x:int, n: int | x:int, n: int) : (int|int)
    requires { Both(n > 0) }
    requires { Both(x >= 0) }
    requires { x =:= x }
    ensures { result =:= result }
  = Var y : int | y : int in
    Var z : int | z : int in
    Var w : int | w : int in
    |_ y := x _|;
    |_ z := 0 _|;
    |_ w := 0 _|;
    While (y > 0) | (y > 0) . <| w <> 0 <] | [> w <> 0 |> do
      invariant { y =:= y }
      invariant { Both (0 <= y /\ y <= x) }
      invariant { Both (0 <= w /\ w < n) }
      invariant { z =:= z }
      variant { [> (n - w) mod n >] }
      If (w = 0) | (w = 0) then
         ( havoc z | skip ); HavocR z { z =:= z };
         |_ y := y - 1 _|;
      end;
      |_ w := (w + 1) mod n _|;
    done;
    |_ result := z _|;
 */

procedure loop (x1: int, n1: int, x2: int, n2: int)
  returns (z1: int, z2: int)

  requires n1 > 0 && n2 > 0;
  requires x1 >= 0 && x2 >= 0;
  requires x1 == x2;
  ensures z1 == z2;
{

  var y1: int; var y2: int;
  var w1: int; var w2: int;

  // locals for snapshots
  var ro: bool;
  var vnt: int;

  y1 := x1; y2 := x2; // |_ y := x _|
  z1 := 0;  z2 := 0;  // |_ z := 0 _|
  w1 := 0;  w2 := 0;  // |_ w := 0 _|

  // While (y > 0) | (y > 0) . <| w <> 0 <] | [> w <> 0 |> do
  while (y1 > 0 || y2 > 0)
    // y =:= y
    invariant y1 == y2;

    // Both (0 <= y /\ y <= x)
    invariant 0 <= y1 && y1 <= x1;
    invariant 0 <= y2 && y2 <= x2;

    // Both (0 <= w /\ w < n)
    invariant 0 <= w1 && w1 < n1;
    invariant 0 <= w2 && w2 < n2;

    // z =:= z
    invariant z1 == z2;

    // adequacy of the loop
    invariant (
      // LO
      (y1 > 0 && w1 != 0) ||
      // RO
      (y2 > 0 && w2 != 0) ||
      // JO
      (y1 > 0 && y2 > 0 && w1 == 0 && w2 == 0) ||
      // done
      (y1 <= 0 && y2 <= 0)
    );
  {

    // snapshot variant [> (n - w) mod n >]
    vnt := (n2 - w2) mod n2;
    // snapshot RO condition
    ro := (y2 > 0 && w2 != 0);

    if (w1 == 0 && w2 == 0)
    {
      havoc z1; // (havoc z | skip)

      assert (exists v: int :: z1 == v); // added by chk

      havoc z2; // HavocR z { z := z }
      assume z1 == z2;

      y1 := y1 - 1; y2 := y2 - 1; // |_ y := y - 1 _|
    }

    // |_ w := (w + 1) mod n _|
    w1 := (w1 + 1) mod n1; w2 := (w2 + 1) mod n2;

    // variant decreases on RO
    assert ro ==> (0 <= ((n2 - w2) mod n2));
    assert ro ==> ((n2 - w2) mod n2) < vnt;
  }
}
