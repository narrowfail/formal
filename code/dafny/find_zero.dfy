// a where conigous items are equal or differ by 1:
// a[i-1]==a[i] || a[i-1]==a[i]+1
method findzero (a:array<int>) returns (i:int)
requires a != null;
requires forall i :: 0 <= i < a.Length ==> a[i] >= 0;
requires forall i :: 0< i <a.Length ==> a[i] >= a[i-1] - 1;
ensures 0 <= i <= a.Length;
ensures forall j :: 0<= j < i ==> a[j] != 0;
ensures i == a.Length || a[i]==0;
{
    i:=0;
    while (i != a.Length && a[i] != 0)
    invariant 0 <= i <= a.Length;
    invariant forall j :: 0 <= j < i ==> a[j] != 0;
    {
        no_zero(a,i);
        i := min(i+a[i], a.Length);
    }
}

function method min(a:int, b:int):int
{
    if a < b then a else b
}

// We demostrate that there are no ceros from i to a[i]+i
// Without modifying the array, we show Dafny that Pre => Post.
lemma no_zero (a:array<int>, i: int)
requires a !=null;
requires forall i :: 0 <= i < a.Length ==> a[i] >= 0;
requires forall i :: 0 < i< a.Length ==> a[i] >= a[i-1]-1;
requires 0 <= i < a.Length;
requires a[i] != 0;
ensures forall j :: i <= j < min(a[i]+i, a.Length) <= a.Length ==> a[j] != 0;
{
    var k: int;
    k := i;
    while (k != min(a[i]+i, a.Length))
    invariant i <= k <= min(a[i]+i, a.Length);
    invariant forall j :: i <= j < k ==> a[j] != 0;
    invariant k != min(i+a[i], a.Length) ==> a[k] >= a[i]-(k-i) > 0;
    {
        k := k + 1; 
    }
}

