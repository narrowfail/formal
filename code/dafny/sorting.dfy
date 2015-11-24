// Sorted predicate between indexes
predicate sorted(a: array<int>, low: int, high :int)
    requires a != null;
    requires 0 <= low <= high <= a.Length;
    reads a;
    {
        forall j, k :: low <= j < k < high ==> a[j] <= a[k]
    }

predicate leq_partitioned(a:array<int>, r:int)
    reads a;
    requires a != null;
    {
        forall j, k :: 0 <= j < r <= k < a.Length ==> a[j] <= a[k]
    }

method bubble_sort(a:array<int>)
    modifies a;
    requires a != null;
    ensures multiset(a[..]) == old(multiset(a[..]));
    ensures sorted(a,0,a.Length)
    {
        var r:int;
        r := a.Length;
        while(r != 0)
        invariant a.Length >= r >= 0;
        invariant multiset(a[..]) == old(multiset(a[..]));
        invariant sorted(a,r,a.Length);
        invariant leq_partitioned(a,r);
        {
            var i : int;
            i := 0;
            while(i+1 != r)
            invariant 0 <= i < r;
            invariant forall j :: 0 <= j < i ==> a[j] <= a[i];
            invariant leq_partitioned(a,r);
            invariant sorted(a,r,a.Length);
            invariant multiset(a[..]) == old(multiset(a[..]));
            {
                if(a[i] > a[i+1]) {
                    a[i], a[i+1] := a[i+1], a[i];
                }
                else {}
                i := i+1 ;
            } 
            r := r-1 ;
        }
    }