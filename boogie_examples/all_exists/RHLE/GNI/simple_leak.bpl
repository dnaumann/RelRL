/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/gni/simple-leak.imp
*/


var low_1, low_2, high_1, high_2 : int;

// should not and does not verify
procedure biprog () returns (ret_1, ret_2: int)
  requires low_1 == low_2;
  ensures low_1 == low_2;
  ensures ret_1 == ret_2;
{
    ret_1 := high_1 + low_1;
    ret_2 := high_2 + low_2;
}