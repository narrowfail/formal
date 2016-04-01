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
predicate sorted(a:array<int>, l:int, u:int)
	reads a
	requires a != null
	{
		forall j, k :: 0 <= l <= j <= k < u <= a.Length ==> a[j] <= a[k]
	}

// Belongs to array predicate
predicate array_member(a : array<int>, l : int, u : int, x : int)
	reads a;
	requires a != null;
	{
		0 <= l <= u < a.Length && exists j :: l <= j <= u && a[j] == x
	}

method binary_search(a : array<int>, x : int) returns (i : int)
	requires a != null;
	requires sorted(a, 0, a.Length);
	ensures (0 <= i < a.Length && a[i] == x) ||
			(i == a.Length && !array_member(a,0,a.Length-1,x))
	{
		var l, r : int;
		l,r := 0, a.Length-1 ;
		i := (l+r)/2;
		while l <= r && x != a[i]
		invariant  0 <= l <= a.Length
		invariant -1 <= r < a.Length
		invariant i == (l+r)/2
		invariant array_member(a,0,a.Length-1,x) ==> array_member(a,l,r,x)
		{
			if x < a[i] {r := i-1;}
			else if x > a[i] {l := i+1;}
			i:=(l+r)/2;
		}
		if r<l {i:=a.Length;}
	}		
