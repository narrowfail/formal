// Bitwise operations needed for crypto.

//method Main() {
//    //Simple test
//    var a := new bool[3]; // 3 element array of ints
//    a[0], a[1], a[2] := true, false, true;
//    shift_right(a);
//    print a[0];
//    print a[1];
//    print a[2];
//}

method shift_right(a:array<bool>)
    modifies a;
    requires a != null;
    requires a.Length > 1;
    //ensures multiset(a[..]) == old(multiset(a[..]));
    {
        var i : int;
        var tmp : bool;
        i := a.Length - 1;
        // Store the last element
        tmp := a[a.Length - 1];

        while(i > 0)
        invariant 0 <= i < a.Length;
        {
            a[i] := a[i-1];
            i := i - 1;
        }
        a[0] := tmp;
        //assert(multiset(a[..]) == old(multiset(a[..])));
    }