method has_sequential(a: array<int>, key: int) returns (ret: int)
    requires a != null
    requires a.Length > 0
    {
        //Ini
        var index: int;
        ret := -1;
        index := 0;

        while (index < a.Length)
        invariant 0 <= index <= a.Length
        decreases  a.Length - index
        {
            if a[index] == key {
                ret := index;
            }
            index := index + 1;
        }
    }


//has binary
