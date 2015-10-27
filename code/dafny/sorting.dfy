// Sorted predicate between indexes
predicate sorted(a: array<int>, low: int, high :int)
    requires a != null
    requires 0 <= low <= high <= a.Length
    reads a
    {
        forall j,k ::low <= j < k < high ==> a[j] <= a[k]
    }


// Recursive count
function count(item: int, a: seq<int>): nat
{
    if |a|== 0 then 0
    else if item == a[0] then 1 + count(item, a[1..])
         else count(item, a[1..])
}


// Is permutation method
predicate perm(a: seq<int>, b: seq<int>)
    requires |a| == |b|
    {
      forall t :: count(t, a) == count(t, b)
    }


method swap(a: array<int>, first: nat, second: nat)
    requires a != null
    requires a.Length > 0
    requires 0 <= first < a.Length
    requires 0 <= second < a.Length
    modifies a
    ensures old(a.Length) == a.Length
    ensures old(a[first]) == a[second]
    ensures old(a[second]) == a[first]
    ensures perm(a[..], old(a[..]))
    {
        //Init
        var tmp: int;
        tmp := a[first];
        a[first] := a[second];
        a[second] := tmp;
    }