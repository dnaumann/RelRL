/*

This example was done in BoogieExamples.bpl but the encoding
is a little ad hoc (simplified in ways that make it 
non-obvious that it's in accord with the standard translation).

This file again starts from the WhyRel
version (copied below) but encodes it more closely to the 
WhyRel encoding of bi-while which is 
all_exists/Conditional_Loop/prog.rl.

In fact we do two versions, to illustrate a technical point.

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

/* First version: simple non-exclusive alignment conditions; fails
   to verify unless the RO snapshot include exclusion condition.
   We add it here --see NOTE-- but that diverges from def of chk
   function for filter-adequacy. */

procedure loop1 (x1: int, n1: int, x2: int, n2: int)
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

    // snapshot variant [> (n - w) mod n >] (added by chk)
    vnt := (n2 - w2) mod n2;
    // snapshot RO condition (added by chk)
    ro := (y2 > 0 && w2 != 0) 
         && !(y1 > 0 && w1 != 0); // NOTE: not really added by chk

    // left-only condition
    if (y1 > 0 && w1 != 0)
    {  // left projection of body
       if (w1 == 0)
       { havoc z1; y1 := y1 - 1; }
       w1 := (w1 + 1) mod n1; 
    } 
    // right-only condition 
    else if (y2 > 0 && w2 != 0)
    {  // bi-right projection of body
       if (w2 == 0)
       { assert (exists v: int :: z1 == v); // added by chk
         havoc z2; // HavocR z { z := z }
         assume z1 == z2;    
         y2 := y2 - 1; 
       }
       w2 := (w2 + 1) mod n2;         
     }
     else 
     { // an alignment of body
       assert w1 == 0 <==> w2 == 0;
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
     } 

    // variant decreases and lower bounded on RO (added by chk)
    assert ro ==> (0 <= ((n2 - w2) mod n2));
    assert ro ==> ((n2 - w2) mod n2) < vnt; // NOTE: fails without NOTE above
  }
}




/* Second version: formulate the alignment conditions to be 
   mutually exclusive, and strictly follow the RO snapshot in 
   def of chk for filter-adequacy. */

procedure loop2 (x1: int, n1: int, x2: int, n2: int)
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

  // While (y > 0) | (y > 0) . 
  //    <| w <> 0 <] | !(y1 > 0 && w1 <> 0) && [> w <> 0 |> do
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

    // snapshot variant [> (n - w) mod n >] (added by chk)
    vnt := (n2 - w2) mod n2;
    // snapshot RO condition (added by chk)
    ro := (y2 > 0 && w2 != 0 && !(y1 > 0 && w1 != 0));

    // left-only condition
    if (y1 > 0 && w1 != 0)
    {  // left projection of body
       if (w1 == 0)
       { havoc z1; y1 := y1 - 1; }
       w1 := (w1 + 1) mod n1; 
    } 
    // right-only condition 
    else if (y2 > 0 && w2 != 0 && !(y1 > 0 && w1 != 0))
    {  // bi-right projection of body
       if (w2 == 0)
       { assert (exists v: int :: z1 == v); // added by chk
         havoc z2; // HavocR z { z := z }
         assume z1 == z2;    
         y2 := y2 - 1; 
       }
       w2 := (w2 + 1) mod n2;         
     }
     else 
     { // an alignment of body
       assert w1 == 0 <==> w2 == 0;
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
     } 

    // variant decreases and lower bounded on RO (added by chk)
    assert ro ==> (0 <= ((n2 - w2) mod n2));
    assert ro ==> ((n2 - w2) mod n2) < vnt;
  }
}
