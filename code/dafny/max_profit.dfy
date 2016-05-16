/*
Suppose we could access yesterday's stock prices as a list, where:

The indices are the time in minutes past trade opening time, which was 9:30am local time.
The values are the price in dollars of Apple stock at that time.
So if the stock cost $500 at 10:30am, stock_prices_yesterday[60] = 500.

Write an efficient function that takes stock_prices_yesterday and returns the 
best profit I could have made from 1 purchase and 1 sale of 1 Apple stock yesterday.

Source: https://www.interviewcake.com/question/python/stock-price
*/

predicate segment_min (a : array<int>, l : int, u : int, m : int) 
	reads a;
	requires a != null;
	requires 0 <= l < u <= a.Length;
	{
		l <= m < u && forall j :: l <= j < u ==> a[m] <= a[j]
	}

predicate segment_max_diff (a : array<int>, l : int, u : int, left : int, right : int)
	reads a;
	requires a != null;
	requires 0 <= l < u <= a.Length;
	{
		l <= left < right < u && 
		forall j, k :: l <= j < k < u ==> a[k] - a[j] <= a[right] - a[left]
	}

method max_profit (a : array<int>) returns (l : int, r : int)
	requires a != null;
	requires a.Length >= 2;
	ensures segment_max_diff (a, 0, a.Length, l, r);
	{
		var i, m : int;
		i, m, l, r := 2, if a[0] <= a[1] then 0 else 1, 0, 1 ; 
		while i != a.Length
		invariant 2 <= i <= a.Length;
		invariant segment_min (a, 0, i, m);
		invariant segment_max_diff (a, 0, i, l, r);
		{
			if (a[i] - a[m] > a[r] - a[l]){
				l,r := m,i ;
			}
			if (a[i] < a[m]){
				m := i ;
			}
			i := i + 1;
		}
	}