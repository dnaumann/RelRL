/*

// A simple deterministic program that does not use its parameter at all.

expected: valid;

forall: unused[1];
exists: unused[2];

pre:  (not (= unused!1!param unused!2!param));
post: (= unused!1!ret   unused!2!ret);

fun unused(param) {
  ret := 5;
  return ret;
}

*/

// verifies
procedure biprog (param1, param2: int) returns (ret1, ret2: int)
    requires (!(param1 == param2));
    ensures (ret1 == ret2);
{
    ret1 := 5; ret2 := 5;
}