method Main(){
    var i:int;
    var a := new int[5];
    a[0],a[1],a[2],a[3],a[4] := 0,1,8,3,4;
    i := max(a);
    print "Max:";
    print i;
    print "\n";
}


method max(a: array<int>) returns (mx: int)
    requires a != null
    {
        var index, current: int;
        //Ini
        index := 0;
        mx := 0;

        while (index < a.Length)
        invariant index <= a.Length
        decreases  a.Length - index
        {
            if a[index] > mx {
                mx := a[index];
            }
            index := index + 1;
        }
    }

