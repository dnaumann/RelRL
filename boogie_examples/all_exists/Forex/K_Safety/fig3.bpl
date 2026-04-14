/*
[forall]
int x;
int n;
int c;
int o; 

c = 0;

while (x < n) {
    x = x + 1;
    c = c + o;
}

[forall]
int x;
int n;
int c;
int o; 

c = 0;

while (x < n) {
    x = x + 1;
    c = c + o;
}


[pre]

x_0 == x_1
&&
n_0 == n_1
&&
o_0 == o_1

[post]

c_0 == c_1

*/

var c, c': int;
var x, x': int;
var n, n': int;
var o, o': int;

// verifies
procedure biprog () 
  requires  n == n' &&
            x == x' &&
            o == o';
  ensures ((c == c'));
  modifies c, c', x, x';
{

    c := 0; c' := 0;

    while (x < n || x' < n')
        invariant c == c';
        invariant x < n <==> x < n;
    {
        x := x + 1; x' := x' + 1;
        c := c + o; c' := c' + o';
    }

}