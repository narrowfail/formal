// Common power method
function method pow(a: int, b: int): int
    // Dafny fails to ensure  pow(m,2*n) == pow(m*m,n) (lemma below)
    requires b >= 0;
    {
        if b == 0 then 1
        else if b == 1 then a
        else a * pow(a, b - 1)
    }

// Simple Power
method power_simple(a: nat, b: nat) returns (r: int)
    requires b >= 0;
    ensures r == pow(a, b);
    {
        var x: int;
        // Init
        x := 0;
        r := 1;

        while (x != b)
        invariant 0 <= x <= b;
        invariant r == pow(a, x);
        decreases b - x;
        {
            r := r * a;
            x := x + 1;
        }
    }


lemma L_pr_pow (m:int, n:int)
    requires m >= 0 && n >= 0;
    ensures pow(m*m,n) == pow(m,2*n);
    {}


// Power binary
method power_binary(m:int, n:int) returns (r:int)
    requires m >= 0 && n >= 0;
    ensures r == pow(m,n);
    {
        var x:int, y:int;
        x,y,r := m,n,1 ;
        while y != 0
        invariant x >= 0 && y >= 0;
        invariant pow(m,n) == r * pow(x,y);
        {
            if y % 2 == 0 {
                // assert pow(x,y) == pow(x,2*(y/2));
                L_pr_pow (x,y/2); // Lemma. Dafny unable to prove directly
                x, y := x*x, y/2;
            }
            else {
                y, r := y - 1, r * x;
            }
        }
}