/*

[forall]
int a;
int x;
int t;

a = 0;
x = *;
while (t > 0) {
    t = t - 1;
    a = a + x;
}

[forall]
int a;
int x;
int t;

a = 0;
x = *;
while (t > 0) {
    t = t - 1;
    a = a + x;
}

[exists]
int a;
int x;
int t;

a = 0;
x = *;
while (t > 0) {
    t = t - 1;
    a = a + x;
}

[pre]
t_0 == t_1 
&& 
t_1 == t_2

[post]
a_2 == a_0 + a_1

[maxC]
3

*/