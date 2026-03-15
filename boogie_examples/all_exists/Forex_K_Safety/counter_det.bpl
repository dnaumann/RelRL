/*
[forall]
int c;
int x;
int n;

c = 0;

while (x < n) {
    x = x + 1;
    c = c + 1;
}



[forall]
int c;
int x;
int n;

c = 0;

while (x < n) {
    x = x + 1;
    c = c + 1;
}

[pre]

n_0 == n_1
&&
x_0 == x_1

[post]

c_0 == c_1

*/

var c, c': int;
var x, x': int;
var n, n': int;

// verifies
procedure biprog () 
  requires  n == n' &&
            x == x';
  ensures ((c == c'));
  modifies c, c', x, x';
{

    c := 0; c' := 0;

    while (x < n || x' < n')
        invariant c == c';
        invariant x < n <==> x < n;
    {
        x := x + 1; x' := x' + 1;
        c := c + 1; c' := c' + 1;
    }

}
