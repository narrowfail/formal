// Common power method
function method pow(a: int, b: int): int
    requires b >= 0
    {
        if b == 0 then 1
        else if b == 1 then a
        else a * pow(a, b - 1)
    }

// Exponentiation by successive squaring.
method power_binary(a: int, b: int) returns (ret: int)
    requires b >= 0
    // TODO Check
    // ensures ret == pow(a, b)
    {
        // Init
        var x, y: int;
        ret := 1;
        x := a;
        y := b;

        while (y != 0)
        invariant  y >= 0
        //TODO check invariant
        //invariant  ret * pow(x, y) == pow(a, b)
        decreases y
        {
          if (y % 2 == 0)
          {
             x := x * x;
             y := y / 2;
          }
          else
          {
             ret := ret * x;
             y := y - 1;
          }
        }
    }
