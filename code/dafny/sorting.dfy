// Sorted predicate between indexes
predicate sorted(a: array<int>, low: int, high :int)
    requires a != null;
    requires 0 <= low <= high <= a.Length;
    reads a;
    {
        forall j, k ::low <= j < k < high ==> a[j] <= a[k]
    }


// Swap two items from an array
method swap<T>(a: array<T>, first: nat, second: nat)
    requires a != null;
    requires a.Length > 0;
    requires 0 <= first < a.Length;
    requires 0 <= second < a.Length;
    modifies a;
    ensures old(a.Length) == a.Length;
    ensures old(a[first]) == a[second];
    ensures old(a[second]) == a[first];
    ensures forall m :: 0 <= m < a.Length && m != first
                        && m != second ==> a[m] == old(a[m]);
    ensures multiset(a[..]) == old(multiset(a[..]));
    {
        // Init
        a[first], a[second] := a[second], a[first];
    }


method bubble_sort(a: array<int>)
    requires a != null;
    modifies a;
    ensures multiset(a[..]) == old(multiset(a[..]));
    //ensures sorted(a, 0, a.Length);
    {
        var r: int;
        // Init
        r := a.Length;

        while (r !=0 )
        invariant 0 <= r <= a.Length;
        invariant multiset(a[..]) == old(multiset(a[..]));
        //invariant sorted(a, r, a.Length);
        //invariant forall j, k : int :: j >= 0 && j < r && r <= k < a.Length ==> a[j] <= a[k];
        decreases r;
        {
            var i: int;
            // Init
            i := 0;

            while (i+1 != r)
            invariant 0 <= i < r;
            //invariant forall j : int :: j >= 0 && j < i ==> a[j] <= a[i];
            invariant multiset(a[..]) == old(multiset(a[..]));
            decreases r - i;
            {
                // Order element
                if(a[i] > a[i+1]){
                    swap(a, i, i+1);
                }
                // Loop increment
                i := i + 1;
            }
            // Loop decrement
            r := r - 1;
        }
    }

// 1,8,2