/*

[forall]
int x;
int y;
int z;

y = 0;
z = x;

while (z > 0) {
    z = z - 1;
    y = y + x;
}



[forall]
int x;
int y;
int z;

y = 0;
z = x;

while (z > 0) {
    z = z - 1;
    y = y + x;
}


[pre]

x_0 == x_1

[post]

y_0 == y_1
*/

var x, x': int;
var y, y': int;
var z, z': int;

// verifies
procedure biprog () 
  requires x == x';
  ensures  y == y';
  modifies y, y', x, x', z, z';
{

    y := 0; y' := 0;
    z := x; z' := x';

    while (z > 0 || z' > 0)
        invariant y == y';
        invariant  z == z'; 
    {
        z := z - 1; z' := z' - 1;
        y := y + x; y' := y' + x';
    }


}
