/*

https://github.com/rcdickerson/rhle-benchmarks/blob/main/param-usage/even-odd.imp
*/


// should not and does not verify
procedure biprog (param1, param2: int) returns (ret1, ret2: int)
    requires (!(param1 == param2));
    ensures (ret1 == ret2);
{
    ret1 := param1 mod 2; ret2 := param2 mod 2;
}