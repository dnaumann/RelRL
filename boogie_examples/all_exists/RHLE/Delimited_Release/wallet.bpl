/*
https://github.com/rcdickerson/rhle-benchmarks/blob/main/delimited-release/wallet.imp

*/

var funds1, spent1, cost1, funds2, spent2, cost2 : int;

procedure skip () returns ();

procedure biprog () returns ()
  requires spent1 == spent2 && cost1 == cost2;
  requires funds1 >= cost1 && funds2 >= cost2; // delimited release
  modifies funds1, spent1, cost1, funds2, spent2, cost2; 
  ensures spent1 == spent2;
{
    if (funds1 >= cost1)
    {
      funds1 := funds1 - cost1;
      spent1 := spent1 + cost1;
    }
    else
    {
      call skip();
    }

    if (funds2 >= cost2)
    {
      funds2 := funds2 - cost2;
      spent2 := spent2 + cost2;
    }
    else
    {
      call skip();
    }
}