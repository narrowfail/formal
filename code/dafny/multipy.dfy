// Mutiply using sum
method mutiply_sum(a: int, b: int) returns (r: int)
    requires b > 0;
    ensures r == a*b;
    {
        var x: int;
        //Init
        r := 0;
        x := 0;

        while (x != b)
        invariant 0 <= x <= b;
        invariant r == a * x;
        decreases  b - x;
        {
            r := r + a;
            x := x + 1;
        }
    }

