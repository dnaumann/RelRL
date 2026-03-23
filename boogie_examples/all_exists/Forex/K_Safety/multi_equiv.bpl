/*

[forall]
int x;
int n;
int c;

x = 0;
while (0 < n) {
    n = n - 1;
    x = x + c;
    x = x + c;
}

[forall]
int x;
int n;
int c;

x = 0;
while (0 < n) {
    n = n - 1;
    x = x + (c + c);
}

[pre]
n_0 == n_1
&&
c_0 == c_1


[post]
x_0 == x_1

*/

var x, x': int;
var n, n': int;
var c, c': int;

// verifies
procedure biprog () 
  requires  n == n' &&
            c == c';
  ensures ((x == x'));
  modifies n, n', x, x';
{

    x := 0; x' := 0;

    while (0 < n || 0 < n')
        invariant n == n';
        invariant x == x';
    {
        n := n - 1; n' := n' - 1;
        x := x + c;
        x := x + c;
        x' := x' + (c' + c');
    }

}