// Functional sum.
function func_sum(a: array<int>, min: int, max:int): int
    requires a != null;
    requires 0 <= min <= max < a.Length;
    reads a;
    decreases max - min;
    {
		if min != max then
			func_sum(a, min + 1, max) + a[min]
		else
			a[min]
    }

// Array sum
method array_sum(a: array<int>) returns (sum: int)
    requires a != null;
    requires a.Length > 0;
    {
        var index: int;
        // Init
        index := 0;
        sum := 0;

        while (index < a.Length)
        invariant 0 <= index <= a.Length
        // invariant sum == func_sum(a, 0, index);
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
