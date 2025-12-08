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
if (x >= l) {
    skip;
} else {
    while (true) {
        skip;
    }
}

[pre]
l_0 == l_1

[post]
x_0 == x_1

[inv]
x_0 >= l_0

[maxC]
1

*/

procedure skip () returns ()
          modifies ;
{ }

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

    if (x2 >= l2)
    {
        call skip();
    }
    else
    {        
        while (true) { 
           call skip(); 
        }
    }

}