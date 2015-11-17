// Write functional verion.

// Array sum
method array_sum(a: array<int>) returns (sum: int)
    requires a != null;
    requires a.Length > 0;
    //TODO ensure result is SUM
    {
        var index: int;
        // Init
        index := 0;
        sum := 0;

        while (index < a.Length)
        invariant 0 <= index <= a.Length
        //invariant forall j : int :: (j >= 0 && j < index ==> sum(a[0..j]))
        decreases  a.Length - index
        {
            sum := sum + a[index];
            index := index + 1;
        }
    }


// Array prod
method array_prod(a: array<int>) returns (prod: int)
    requires a != null;
    requires a.Length > 0;
    //TODO ensure result is PROD
    {
        var index: int;
        // Init
        index := 0;
        prod := 1;

        while (index < a.Length)
        invariant 0 <= index <= a.Length
        //invariant forall j : int :: (j >= 0 && j < index ==> prod(a[0..j]))
        decreases  a.Length - index
        {
            prod := prod * a[index];
            index := index + 1;
        }
    }
