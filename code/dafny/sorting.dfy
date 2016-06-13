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

// Insertion Sort
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


// Selection Sort
method selection_sort(a:array<int>)
    modifies a;
    requires a != null;
    requires a.Length > 0;
    ensures multiset(a[..]) == old(multiset(a[..]));
    ensures sorted(a, 0, a.Length);
    {
        var min, i : int;
        i := 0;
        while(i < a.Length - 1)
        invariant 0 <= i < a.Length;
        invariant multiset(a[..]) == old(multiset(a[..]));
        invariant sorted(a,0,i);
        invariant forall j, k :: 0 <= j < i <= k < a.Length ==> a[j] <= a[k];
        {
            min := select(a, i);
            // Swap
            a[i], a[min] := a[min], a[i];
            // Step
            i := i + 1;
            
        }
    }

method select(a:array<int>, i :int) returns (m: int)
    requires a != null;
    requires 0 <= i < a.Length;
    ensures multiset(a[..]) == old(multiset(a[..]));
    ensures i <= m < a.Length;
    ensures forall x :: i <= x < a.Length ==> a[m] <= a[x];
    {
        var j := i;
        m := j;
        while(j < a.Length - 1)
        invariant i <= j < a.Length;
        invariant i <= m < a.Length;
        invariant forall x :: i <= x <= j ==> a[m] <= a[x];
        invariant multiset(a[..]) == old(multiset(a[..]));
        {
            j := j + 1;
            if (a[j] < a[m]){
                m := j;
            }
        }
    }


// Dutch National Flag - 0 = red, 1 = white, 2 = blue 
method dnf(a: array<int>) 
    modifies a;
    requires a != null;
	requires forall x :: 0 <= x < a.Length ==> (a[x] == 0 || a[x] == 1 || a[x] == 2);
    ensures sorted(a, 0, a.Length);     // Flag order
    ensures multiset(a[..]) == old(multiset(a[..]));
	{
		var low, mid, hig : int;
		low, mid, hig := 0, 0, a.Length;
		while(mid != hig)
		invariant 0 <= low <= mid <= hig <=  a.Length;
        invariant forall x :: 0 <= x < a.Length ==> (a[x] == 0 || a[x] == 1 || a[x] == 2);
		// Flag order:
		invariant forall x :: 0 <= x < low ==> a[x] == 0;
		invariant forall y :: low <= y < mid ==> a[y] == 1;
		invariant forall z :: hig <= z < a.Length ==> a[z] == 2;
		// Permutation
		invariant multiset(a[..]) == old(multiset(a[..]));
		{
			// Red
			if (a[mid] == 0)
			{
				a[low], a[mid] := a[mid], a[low];
				low := low + 1;
				mid := mid + 1;
			}
			else {
				// White
				if (a[mid] == 1){
					mid := mid + 1;
				}
				else {
				    // Blue
				    hig := hig - 1;
					a[hig], a[mid] := a[mid], a[hig];
				}
			}
		}
	}

//  Dutch National Flag - 0 = red, 1 = white, 2 = blue 
datatype Color = red|white|blue

predicate color_sorted(a: Color, b: Color) 
{
    a == red || b == blue || a == b
}

method dnf2(a:array<Color>)
    modifies a;
    requires a != null;
    ensures forall i, j :: 0 <= i < j < a.Length ==> color_sorted(a[i],a[j]);
    ensures multiset(a[..]) == old(multiset(a[..]));
    {
      var r, w, b := 0, 0, a.Length;
      while ( w != b)
      invariant 0 <= r <= w <= b <= a.Length
      invariant forall i :: 0 <= i < r ==> a[i] == red;
      invariant forall i :: r <= i < w ==> a[i] == white;
      invariant forall i :: b <= i <a.Length ==> a[i] == blue;
      invariant multiset(a[..]) == old(multiset(a[..]));
      {
        match a[w]
          {
              case red => a[r], a[w] := a[w], a[r]; r := r + 1; w := w + 1;
              case white => w := w + 1;
              case blue => b := b - 1; a[w], a[b] := a[b], a[w];
          }
      }
    }


// Quck Sort
method quick_sort(a:array<int>, start:int, end:int)
    modifies a;
    requires a != null;
    requires a.Length > 0;
	requires 0 <= start <= end <= a.Length;
    
	// Pivot
	requires 0 <= start <= end < a.Length ==> forall j :: start <= j < end ==> a[j] < a[end];
	requires 0 < start <= end <= a.Length ==> forall j :: start <= j < end ==> a[start - 1] <= a[j];

	// Sorted
	ensures sorted(a, 0, a.Length);
	ensures multiset(a[..]) == old(multiset(a[..]));
	
	// Pivot in correct place
	ensures 0 <= start <= end < a.Length ==> forall j :: start <= j < end ==> a[j] < a[end];
	ensures 0 < start <= end <= a.Length ==> forall j :: start <= j < end ==> a[start - 1] <= a[j];
	
	decreases end - start;
    {
        var pivot : int;
		if (start < end) {
			pivot := divide(a, start, end);
 
			// Ordeno la lista de los menores
			quick_sort(a, start, pivot - 1);
 
			// Ordeno la lista de los mayores
			quick_sort(a, pivot + 1, end);
		}
    }

// Pivote
method divide(a:array<int>, start:int, end:int) returns (pivot: int)
	modifies a;
    requires a != null;
	requires a.Length > 0;
    requires 0 <= start < end <= a.Length;
    requires 0 <= start <= end < a.Length ==> forall j :: start <= j < end ==> a[j] < a[end];
    requires 0 < start <= end <= a.Length ==> forall j :: start <= j < end ==> a[start - 1] <= a[j];
    ensures 0 <= start <= pivot < end <= a.Length;
    ensures forall j :: start <= j < pivot ==> a[j] < a[pivot];
    ensures forall j :: pivot < j < end ==> a[pivot] <= a[j];
	ensures multiset(a[..]) == old(multiset(a[..]));
    ensures 0 <= start <= end < a.Length ==> forall j :: start <= j < end ==> a[j] < a[end];
    ensures 0 < start <= end <= a.Length ==> forall j :: start <= j < end ==> a[start - 1] <= a[j];
