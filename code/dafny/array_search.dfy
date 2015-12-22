// Sequential search
method has_sequential(a: array<int>, key: int) returns (ret: int)
    requires a != null
    requires a.Length > 0
    ensures ret >= 0 ==> ret < a.Length && a[ret] == key
    ensures ret < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
    {
        // Ini
        var index: int;
        index := 0;
        ret := -1;

        while (index < a.Length)
        invariant 0 <= index <= a.Length
        invariant forall k :: 0 <= k < index ==> a[k] != key
        decreases  a.Length - index
        {
            if a[index] == key {
                ret := index;
                return;
            }
            index := index + 1;
        }
    }

// Functional version
function sortedf(a: array<int>, index: int): bool
    requires a != null;
    requires index >= 0;
    requires index <= a.Length;
    decreases a.Length - index;
    reads a;
    {
        index == a.Length ||
        index == a.Length - 1 ||
        (a[index] < a[index + 1] && sortedf(a, index + 1))
    }

// Predicate version
predicate sorted(a: array<int>)
    requires a != null
    reads a
    {
       forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
    }

// Binary search
method has_binary(a: array<int>, key: int) returns (ret: int)
    requires a != null;
    requires a.Length > 0;
    requires sorted(a);
    ensures 0 <= ret < a.Length;
    // TODO
    //ensures ret >= 0 ==> ret < a.Length && a[ret] == key
    //ensures ret < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
    {
        var min, max, x: int;
        //Init
        min := 0;
        max := a.Length - 1;
        x := 0;
        ret := min;
        while(max != min)
        invariant 0 <= min <= max < a.Length;
        invariant 0 <= x < a.Length;
        invariant 0 <= min <= ret <= max < a.Length;
        // invariant exists j :: 0 <= j < a.Length ==> a[j] == a[ret];
        decreases max - min;
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
