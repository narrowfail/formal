// Array max one way
method max_one_way(a: array<int>) returns (mx: int)
    requires a != null;
    requires a.Length > 0;
    ensures forall j : int :: j >= 0 && j < a.Length ==> mx >= a[j];
    ensures exists j : int :: j >= 0 && j < a.Length && mx == a[j];
    {
        var index: int;
        // Init
        index := 0;
        mx := a[index];

        while (index < a.Length)
        invariant 0 <= index <= a.Length;
        invariant forall j : int :: j >= 0 && j < index ==> mx >= a[j];
        invariant exists j : int :: j >= 0 && j < a.Length && mx == a[j];
        decreases  a.Length - index;
        {
            if a[index] > mx {
                mx := a[index];
            }
            index := index + 1;
        }
    }


method max_one_way2(a: array<int>) returns (mx: int)
    requires a != null;
    requires a.Length > 0;
    ensures forall j : int :: j >= 0 && j < a.Length ==> mx >= a[j];
    ensures exists j : int :: j >= 0 && j < a.Length && mx == a[j];
    {
        var index: int;
        // Init
        index := a.Length - 1;
        mx := a[index];

        while (index >= 0)
        invariant -1 <= index <= a.Length;
        invariant forall j : int :: j > index && j < a.Length ==> mx >= a[j];
        invariant exists j : int :: j >= 0 && j < a.Length && mx == a[j];
        decreases  index;
        {
            if a[index] > mx {
                mx := a[index];
            }
            index := index - 1;
        }
    }

// Array max 2 way
method max_two_way(a: array<int>) returns (mx: int)
    requires a != null;
    requires a.Length > 0;
    ensures exists j : int :: j >= 0 && j < a.Length && mx == a[j];
    {
        var low, high: int;
        // Init
        low := 0;
        high := a.Length - 1;
        mx := a[low];

        while (low != high)
        invariant 0 <= low <= high < a.Length;
        invariant exists j : int :: j >= low && j <= high && mx == a[j];
        decreases  high - low;
        {
            if a[low] > a[high] {
                high := high - 1;
            }
            else
            {
                low := low + 1;
            }
            mx := a[low];
        }
    }



