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
    //TODO Redundant
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
        //Init
        a[first], a[second] := a[second], a[first];
    }


method bubble_sort(a: array<int>)
    requires a != null;
    modifies a;
    ensures multiset(a[..]) == old(multiset(a[..]));
    ensures sorted(a, 0, a.Length);
    {
        var r: int;
        r := a.Length;
        while (r !=0 )
        invariant 0 <= r <= a.Length;
        invariant sorted(a, r, a.Length);
        invariant forall j, k : int :: j >= 0 && j < r - 1 && r <= k < a.Length ==> a[j] <= a[k]
        {
            var i: int;
            // CODIGO
            r := r -1;
        }
    }