/*

[forall]
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

*/


procedure skip () returns ()
          modifies ;
{ }

procedure biprog (l1: int, l2: int) returns (x1: int, x2: int)
    requires l1 == l2;
    ensures x1 == x2;
{
    var a1: bool; var a2: bool;

    havoc x1;

    if (x1 >= l1)
    {
        call skip();
    }
    else
    {        
        while (true) { 
           call skip(); 
        }
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