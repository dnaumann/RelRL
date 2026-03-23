/*
[forall]
int a;
int b;
int c;

c = 0;
while (a < b) {
    a = a + 1;
    c = c + 1;
}

[forall]
int a;
int b;
int c;

c = 0;
while (a < b) {
    a = a + 1;
    c = c + 1;
}

[pre]

(0 < a_0)
&&
(0 < a_1)
&&
(b_1 < b_0)
&&
(a_0 < b_0)
&&
(a_1 < b_1)
&&
(a_0 < a_1)


[post]

(c_1 < c_0)

*/


var a, a': int;
var b, b': int;
var c, c': int;

// verifies
procedure biprog () 
    returns (res: int, res': int)
  requires  (0 < a) &&
            (0 < a') &&
            (b' < b) &&
            (a < b) &&
            (a' < b') &&
            (a < a');
  ensures c' < c;
  modifies c, c', a, a';
{
    
    c := 0; c' := 0;

    // while (a < b || a' < b') 
    //     invariant a < b <==> a' < b'

    // {
    //     a := a + 1; a' := a' + 1;
    //     c := c + 1; c' := c' + 1;
    // }

    while (a < b)
        invariant (a <= b); 
        invariant c == a - old(a);
    {
        a := a + 1;
        c := c + 1;
    }

    while (a' < b') 
        invariant (a' <= b'); 
        invariant c' == a' - old(a');
    {
        a' := a' + 1;
        c' := c' + 1;
    }

}