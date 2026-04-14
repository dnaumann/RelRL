/*
[forall]
int h;
int x;
int y;
int z;

y = 0;

z = 2 * x;

while (z > 0) {
    z = z - 1;
    y = y + x;
}



[forall]
int h;
int x;
int y;
int z;

y = 0;

z = x;

while (z > 0) {
    z = z - 1;
    y = y + x;
}

y = 2 * y;

[pre]
x_0 == x_1

[post]
y_0 == y_1

[inv]
z_0 == 2 * z_1


[inv]
y_0 == 2 * y_1

[asynchronous]
2
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
    z := 2 * x; z' := x';

    while (z > 0 || z' > 0)
        invariant y == 2 * y';
        invariant  z == 2 * z'; 
    {
        z := z - 1; z' := z' - 1;
        y := y + x; y' := y' + x';

        // unroll left loop once
        if (z > 0)
        {
            z := z - 1;
            y := y + x; 
        }

    }

    y' := 2 * y';


}