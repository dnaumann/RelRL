/*

[forall]
int l;
int h;
int x;
bool a;

x = l;
a = *;
while(a) {
    x = x + 1;
    a = *;
}

[exists]
int l;
int h;
int x;

x = *;
x = if (x <= l) then l else x;

[pre]
l_0 == l_1

[post]
x_0 == x_1

[inv]
x_0 >= l_0

*/


procedure biprog (l1: int, l2: int) returns (x1: int, x2: int)
    requires l1 == l2;
    ensures x1 == x2;
{
    var a1: bool; var a2: bool;

    x1 := l1; 
    havoc a1;
    while (a1)
      invariant x1 >= l1;
    {
        x1 := x1 + 1;
        havoc a1;
    }


    assert ( exists v: int :: v == x1); // inserted by chk
    havoc x2;
    assume x2 == x1;

    if (x2 <= l2)
    {
        x2 := l2;
    }
    else
    {
        x2 := x2;
    }

}