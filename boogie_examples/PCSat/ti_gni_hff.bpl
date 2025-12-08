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
bool a;

x = l;
a = *;
while(a) {
    x = x + 1;
    a = *;
}


[pre]
l_0 == l_1

[post]
x_0 == x_1
*/


procedure biprog (l1: int, l2: int) returns (x1: int, x2: int)
    requires l1 == l2;
    ensures x1 == x2;
{
    var a1: bool; var a2: bool;

    x1 := l1; x2 := l2;

    havoc a1;

    assert ( exists v: bool :: v == a1 ); // inserted by chk
    havoc a2;
    assume a2 == a1;

    while (a1 || a2)
        invariant x1 == x2;
        invariant a1 <==> a2;
    {
        x1 := x1 + 1; x2 := x2 + 1;

        havoc a1;

        assert ( exists v: bool :: v == a1 ); // inserted by chk
        havoc a2;
        assume a2 == a1;


    }

}