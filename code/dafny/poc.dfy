//Testing Alogrithm Derivation Methods in Dafny.

method Main() {
    print "Hello, Dafny\n";
    //Testing sqr
    var vsqr := sqr(10);
    print vsqr;
    print "\n";
    //Testing sqr2
    var vsqr2 := sqr2(10);
    print vsqr2;
    print "\n";
    //Testing exp
    var vexp := exp(2, 8);
    print vexp;
    print "\n";
}



//Power (Function method)
function method exp(a:nat, n:nat): nat
    {
        if n == 0 then 1 else a * exp(a, n-1)
    }

//Some kind of log ... failing!
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

//Failing Method2
//method test(x:nat, n:nat) returns (r:nat)
//    requires (x > 1 && n > 1)
//{
//    r:=x;
//    assert(r==x);
//    r:=r/n;
//    assert(r<x);
//}
