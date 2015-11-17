function div(m:int,n:int) : int
    requires m >= 0
    requires n > 0
    {
        if m < n then 0 else 1 + div (m-n,n)
    }


function rem(m:int,n:int) : int
    requires m >= 0
    requires n > 0
    ensures m == div(m,n)*n + rem(m,n)
    ensures 0 <= rem(m,n) < n 
    {
        if m < n then m else rem (m-n,n)
    }


method nat_division(m:int,n:int) returns (q:int,r:int)
     /*By reduction, replacing m by r. So r determines the rest to be processed
     This gives rem(m,n) == rem(r,n) and also div(m,n) == div(r,n) + q.
     The latter by the idea: final result = what remains op what has already
     been computed.
     */

    requires m >= 0
    requires n > 0 
    ensures q == div(m,n)
    ensures r == rem(m,n)
    {
        // Init
        r,q := m,0 ;
        while (r>=n)
        invariant r >= 0;
        invariant q + div(r,n) == div(m,n);
        invariant rem(r,n) == rem(m,n);
        //decreases r  - Dafny able to infer this.
        {r, q := r-n, q+1;}
    }


method nat_division2(m:int,n:int) returns (q:int,r:int)
    requires m >= 0
    requires n > 0
    ensures m == q*n + r
    ensures r < n
    {
        /* Not quite reduction/advancement...
        Is it a defect of the spec? I don't think so, we should accept
        whatever specification. */

        // Init
        q, r := 0, m;

        while (r >= n)
        invariant m == q*n + r
        //decreases r  - Dafny able to infer this.
        {q, r := q+1, r-n;}
    }