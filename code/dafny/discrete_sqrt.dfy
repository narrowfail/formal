//Discrete square root.
method sqr(x:int) returns (r:int)
    requires x > 0;
    ensures (r*r <= x && (r + 1)*(r+1) > x);
    ensures (r > 0);
    {
        r:=0;
        while (r + 1) * (r + 1) <= x
            invariant r*r <= x
            decreases x-r
        {
            r:= r + 1;
        }
    }


//Discrete square root
method sqr2(x:int) returns (r:int)
    requires x > 0;
    ensures (r*r <= x && (r + 1)*(r+1) > x);
    ensures (r > 0);
    {
        r:=x;
        while r*r > x
            invariant (r + 1)*(r+1) > x
            decreases r
        {
            r:= r - 1;
        }
    }