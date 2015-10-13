function gcd(m: int, n: int): int
    requires m > 0;
    requires n > 0;
    decreases m+n;
    { 
        if (n==m) then n 
        else if (m>n) then gcd(m-n, n) 
        else gcd(m, n-m) 
    }


// Not working yet
method gdc(a: int, b: int) returns (r: int)
    requires  a > 0  &&  b > 0;
    ensures r == gcd(a, b);
    {
        var x: int;
        //Ini
        r := a;
        x := b;

        while (r != x)
        invariant gcd(r, x) == gcd(a, b);
        invariant x > 0;
        invariant r > 0;
        decreases  x+r;
        {
          if (r > x)
          {
             r := r - x;
          }
          else
          {
             x := x - r;
          }
        }
    }

