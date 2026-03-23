/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/param-usage/det-unused.imp
*/

// verifies
procedure biprog (param1, param2: int) returns (ret1, ret2: int)
    requires (!(param1 == param2));
    ensures (ret1 == ret2);
{
    ret1 := 5; ret2 := 5;
}