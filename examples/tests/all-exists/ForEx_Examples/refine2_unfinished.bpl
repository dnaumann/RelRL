[forall]
int x;
int c;
int time; 
int s;

if * {
    x = 0;
    c = 0;
    while (time > 0) {
        time = time - 1;
        x = x + 1;
    }
} else {
    x = 0;
    c = 1;
    while (time > 0) {
        time = time - 1;
        s = *;
        x = x + s;
    }
}


[exists]
int x;
int c;
int time; 
int s;

if * {
    x = 0;
    c = 0;
    while (time > 0) {
        time = time - 1;
        x = x + 1;
        x = x + 1;
    }
} else {
    x = 0;
    c = 1;
    while (time > 0) {
        time = time - 1;
        s = *;
        x = x + s + 1;
    }
}

[pre]
time_0 == time_1

[post]
(c_0 == 0) => (c_1 == 1 && x_0 == x_1)