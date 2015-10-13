method Main(){
    var i:int;
    var a := new int[5];
    a[0],a[1],a[2],a[3],a[4],a[5] := 3,9,1,8,3,4;
    i := max_one_way(a);
    print "Max:";
    print i;
    print "\n";
}


method max_one_way(a: array<int>) returns (mx: int)
    requires a != null
    requires a.Length > 0
    {
        var index, current: int;
        //Ini
        index := 0;
        mx := a[index];

        while (index < a.Length)
        // Pregunta: el limite menor lo infiere? a.low < index < a.lenght
        // Pregunta: Otra inviariante max(a[i..j] = max(a))
        invariant index <= a.Length
        decreases  a.Length - index
        {
            if a[index] > mx {
                mx := a[index];
            }
            index := index + 1;
        }
    }


method max_one_way2(a: array<int>) returns (mx: int)
    requires a != null
    requires a.Length > 0
    {
        var index, current: int;
        //Ini
        index := a.Length - 1;
        mx := a[index];

        while (index >= 0)
        // Pregunta: el limite menor lo infiere? a.low < index < a.lenght
        // Pregunta: Otra inviariante max(a[i..j] = max(a))
        invariant -1 <= index <= a.Length
        decreases  index
        {
            if a[index] > mx {
                mx := a[index];
            }
            index := index - 1;
        }
    }

method max_two_way(a: array<int>) returns (mx: int)
    //Pregunta: En la letra, en el loop solo baja los bordes y no evalua.
    requires a != null
    requires a.Length > 0
    {
        var low, high: int;
        //Ini
        low := 0;
        high := a.Length - 1;

        while (low != high)
        // Pregunta: Otra inviariante max(a[i..j] = max(a))
        invariant 0 <= low <= high < a.Length;
        decreases  high - low
        {
            if a[low] > a[high] {
                high := high - 1;
            }
            else
            {
                low := low + 1;
            }
            mx := a[low];
        }
    }



