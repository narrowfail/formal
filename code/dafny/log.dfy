//LOG failing becuase of non-linear algebra not supported by Dafny!
//method skl(m:nat, n:nat) returns (l:nat, r:nat)
//    requires (m > 0 && n > 1);
//    ensures r > 0;
//    ensures (m == exp(n,l) * r && r%n != 0);
//    {
//        l,r:=0,m;
//        while (r % n == 0)
//            invariant m == exp(n,l) * r
//            invariant r > 1
//            decreases r
//        {
//            l,r:=l+1,r/n;
//        }
//    }

include "exponentiation.dfy" 

// TODO multiple questions
method log_int(a:int, b:int) returns (r: int)
    requires b > 1;
    requires a > 0;
    decreases *;
    //ensures pow(b, r) <= a;
    //ensures pow(b, r + 1) > a;
    {
        var next: int;
        // Init
        r := 0;
        next := power_simple(b, r + 1);

        while (next <= a)
        invariant 0 <= r
        //invariant r < a;
        //invariant pow(b, r) <= a;
        //decreases a - pow(b, r + 1);
        decreases *;
        {
            r := r + 1;
            next := power_simple(b, r + 1);
        }
        return r;
    }

// Python code:
/*def log(a, b):
    r = 0
    next = b ** 1
    while next <= a:
        r = r + 1
        next = b ** (r + 1)
        print "R:%s" % r
        print "B^R:%s" % ((b**r))
        print "A - B^R:%s" % (a - (b**(r+1)))
        #print "r < a | %s" % (r < a)
    print "b ** r <= a | %s" % (b ** r <= a)
    return r*/