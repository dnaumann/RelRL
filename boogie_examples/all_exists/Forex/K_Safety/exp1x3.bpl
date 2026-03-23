/*

[forall]
int x;
int n;

while (x < n) {
    x = x + x;
}

[forall]
int x;
int n;

while (x < n) {
    x = x + x;
}


[pre]

x_0 == x_1
&&
n_0 == n_1

[post]

x_0 == x_1

*/

var x, x': int;
var n, n': int;

// verifies
procedure biprog () 
  requires  n == n' &&
            x == x';
  ensures ((x == x'));
  modifies x, x';
{

    while (x < n || x' < n')
        invariant x == x';
    {
        x := x + x; x' := x' + x';
    }

}
