/*

[forall]
int x;
int y;

x = 1;
y = 2 * x;

while (y > 0) {
    y = y - 1;
    x = 2 * x;
}

[forall]
int x;
int y;

x = 1;
y =  x;

while (y > 0) {
    y = y - 1;
    x = 4 * x;
}

[pre]
x_0 == x_1


[post]
x_0 == x_1

[inv]
y_0 == 2 * y_1

[asynchronous]
2

*/

var x, x': int;
var y, y': int;

// verifies
procedure biprog () 
  requires x == x';
  ensures  x == x';
  modifies y, y', x, x';
{

    x := 1; x' := 1;
    y :=  2 * x; y' :=  x';

    while (y > 0 || y' > 0)
        invariant x == x';
        invariant  y == 2 * y'; 
    {
        y := y - 1; y' := y' - 1;
        x := 2 * x; x' := 4 * x';
    
        // unroll left loop once
        if (y > 0)
        {
            y := y - 1;
            x := 2 * x; 
        }

    }


}