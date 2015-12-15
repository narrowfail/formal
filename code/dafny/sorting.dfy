// Sorted predicate between indexes
predicate sorted(a: array<int>, low: int, high :int)
    requires a != null;
    requires 0 <= low <= high <= a.Length;
    reads a;
    {
        forall j, k :: low <= j < k < high ==> a[j] <= a[k]
    }

// Partitioned less or equal
predicate leq_partitioned(a:array<int>, r :int)
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


method insertion_sort(a:array<int>)
    modifies a;
    requires a != null;
    ensures multiset(a[..]) == old(multiset(a[..]));
    ensures sorted(a,0,a.Length)
    {
        var i : int;
        i := 0;
        while(i < a.Length)
        invariant 0 <= i <= a.Length;
        invariant multiset(a[..]) == old(multiset(a[..]));
        invariant sorted(a,0,i);
        {
            insert(a, i);
            i := i + 1;
        }
    }

method insert(a:array<int>, i :int)
    modifies a;
    requires a != null;
    requires 0 <= i < a.Length;
    requires sorted(a, 0, i);
    ensures sorted(a, 0, i+1);
    ensures multiset(a[..]) == old(multiset(a[..]));
    {
        var j : int;
        j := i;
        while(j > 0 && a[j-1] > a[j])
        invariant 0 <= j <= i;
        invariant sorted(a,0,j);
        invariant sorted(a,j,i+1);
        invariant multiset(a[..]) == old(multiset(a[..]));
        invariant forall m, n :: 0 <= m < j < n <= i ==> a[m] <= a[n];
        invariant a[j] == old(a[i]);
        {
            a[j], a[j-1] := a[j-1], a[j];
            j := j - 1;
        } 
    }