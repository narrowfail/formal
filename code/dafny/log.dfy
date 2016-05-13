include "exponentiation.dfy" 


lemma mon_prod (x : int, y : int)
    requires x > 0;
    requires y > 1;
    ensures x < x*y;
    {
        assert 0 < x*(y-1) == x*y - x;
    }


method skl(m:nat, n:nat) returns (l:nat, r:nat)
    requires (m > 0 && n > 1);
    ensures r > 0;
    ensures (m == pow(n,l) * r && r%n != 0);
    {
        l, r := 0, m;
        while (r % n == 0)
            invariant m == pow(n,l) * r
            //invariant 0 <= l 
            //invariant r > 0
            decreases r
        {
            mon_prod(r/n, n);
            l,r := l+1, r/n;
        }
    }


method log_int(a:int, b:int) returns (r: int)
    requires b > 1;
    requires a > 0;
    ensures r >= 0;
    ensures pow(b, r) <= a;
    ensures pow(b, r + 1) > a;
    {
        var next: int;
        // Init
        r := 0;
        next := power_simple(b, r + 1);

        while (next <= a)
        invariant 0 <= r;
        invariant next == pow(b, r +1);
        invariant pow(b, r) <= a;
        decreases a - pow(b, r + 1);
        {
            r := r + 1;
            next := power_simple(b, r + 1);
        }
        return r;
    }
