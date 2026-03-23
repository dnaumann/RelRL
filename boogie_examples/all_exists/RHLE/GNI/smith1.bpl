/*

https://github.com/rcdickerson/rhle-benchmarks/blob/main/gni/smith1.imp

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

