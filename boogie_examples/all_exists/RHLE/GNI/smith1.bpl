/*


// Example taken from Principles of Secure Information Flow Analysis, Geoffrey Smith, 2006.
// https://users.cis.fiu.edu/~smithg/papers/sif06.pdf

expected: invalid;

forall: smith[1];
exists: smith[2];

post: (= smith!1!ret smith!2!ret);

fun smith(secret) {
  if (secret % 2 == 0) then
    ret := 0;
  else
    ret := 1;
  endif
  return ret;
}

*/

// should not and does not verify
procedure biprog (secret_1, secret_2: int) returns (ret_1, ret_2: int)
  ensures ret_1 == ret_2;
{

    if (secret_1 mod 2 == 0)
    {
      ret_1 := 0;
    }
    else
    {
      ret_1 := 1;
    }

    if (secret_2 mod 2 == 0)
    {
      ret_2 := 0;
    }
    else
    {
      ret_2 := 1;
    }
}

