/*

expected: invalid;

forall: used[1];
exists: used[2];

pre:  (not (= used!1!param used!2!param));
post: (= used!1!ret used!2!ret);

fun used(param) {
  ret := param % 2;
  return ret;
}

*/


// should not and does not verify
procedure biprog (param1, param2: int) returns (ret1, ret2: int)
    requires (!(param1 == param2));
    ensures (ret1 == ret2);
{
    ret1 := param1 mod 2; ret2 := param2 mod 2;
}