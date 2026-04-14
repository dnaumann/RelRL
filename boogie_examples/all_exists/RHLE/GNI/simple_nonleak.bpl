/*

https://github.com/rcdickerson/rhle-benchmarks/blob/main/gni/simple-nonleak.imp
*/

var low_1, low_2, high_1, high_2 : int;

procedure biprog () returns (ret_1, ret_2: int)
  requires low_1 == low_2;
  ensures low_1 == low_2;
  ensures ret_1 == ret_2;
{
    var x1, x2: int;

    x1 := low_1 + high_1; x2 := low_2 + high_2;

    ret_1 := x1 - high_1; ret_2 := x2 - high_2;
}

