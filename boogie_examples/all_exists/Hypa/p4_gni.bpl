/*

[forall]
int o;
int h;

if (h > 0) {
    if * {
        o = 1;
    } else {
        o = 2;
    }
} else {
    if * {
        o = 2;
    } else {
        o = 1;
    }
}


[exists]
int o;
int h;

if (h > 0) {
    if * {
        o = 1;
    } else {
        o = 2;
    }
} else {
    if * {
        o = 2;
    } else {
        o = 1;
    }
}

[pre]
true

[post]
o_0 == o_1

*/

procedure gni () returns (o1: int, o2: int)
          ensures  o1 == o2;
{
    var x1: bool; var x2: bool;
    var h1: int; var h2: int;


    havoc h1;
    if (h1 > 0 )
    {
        havoc x1;
        if (x1)
        {
        o1 := 1;
        }
        else{
        o1 := 2;
        }

    }
    else
    {
        havoc x1;
        if (x1)
        {
            o1 := 2;
        }
        else{
            o1 := 1;
        }

    }

    assert (exists v: int :: v == h1);
    havoc h2;
    assume h2 == h1;
    if (h2 > 0)
    {
        assert (exists v: bool :: v == x1);
        havoc x2;
        assume (x2 == x1);
        if (x2)
        {
        o2 := 1;
        }
        else{
        o2 := 2;
        }

    }
    else
    {
        assert (exists v: bool :: v == x1);
        havoc x2;
        assume (x2 == x1);
        if (x2)
        {
            o2 := 2;
        }
        else{
            o2 := 1;
        }

    }

}
  
