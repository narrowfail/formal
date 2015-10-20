// Sequential search
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

function sorted(a: array<int>, index: int): bool
    requires a != null;
    requires a.Length > 0;
    requires index >= 0;
    requires index < a.Length;
    decreases a.Length - index;
    { 
        if (index == a.Length - 1) then true 
        else if (index < a.Length - 1) then sorted(a, index + 1) 
        else false
    }

// Binary search
method has_binary(a: array<int>, key: int) returns (ret: int)
    requires a != null;
    requires a.Length > 0;
    requires sorted(a, 0);
    // result = 0 => key belongs elements(a)
    {
        var min, max, x: int;
        //Init
        min := 0;
        max := a.Length - 1;
        x := 0;
        while(max != min)
        invariant min >= 0;
        invariant max < a.Length;
        invariant min <= x;
        invariant max >= x;
        //Add invariantL Key belongs to a elements
        //decreases max - min;
        {
            x := (max + min) / 2;
            if a[x] < key {
                min := x + 1;
            } else {
                max := x;
            }
            ret := min;
        }
    }
