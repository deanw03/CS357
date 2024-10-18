method M1(x: int, y: int) returns (r: int)
    // The result r will be the product of x and y.
    ensures r == x * y
    decreases x < 0, x // This helps with termination, as x is decreasing.
{
    if x == 0 {
        // Base case: if x is 0, return 0 since 0 * y = 0.
        r := 0;
    } else if x < 0 {
        // If x is negative, recursively call M1 with -x to handle it as a positive value.
        r := M1(-x, y);
        // Negate the result because multiplying with a negative flips the sign.
        r := -r;
    } else {
        // Recursive case: subtract 1 from x and add y repeatedly using A1.
        r := M1(x - 1, y);
        r := A1(r, y); // A1 adds y to the result, simulating multiplication.
    }
}

method A1(x: int, y: int) returns (r: int)
    // The result r is the sum of x and y.
    ensures r == x + y
{
    r := x; // Start with x.
    
    if y < 0 {
        // If y is negative, decrement r and increment n until y reaches 0.
        var n := y;
        while n != 0
            invariant r == x + y - n // Invariant: tracks how far n is from y.
            invariant -n >= 0 // n should be non-positive in this case.
        {
            r := r - 1; // Decrease r.
            n := n + 1; // Increase n towards 0.
        }
    } else {
        // If y is positive, increment r and decrement n until y reaches 0.
        var n := y;
        while n != 0
            invariant r == x + y - n // Invariant: tracks progress in adding y.
            invariant n >= 0 // n should be non-negative in this case.
        {
            r := r + 1; // Increase r.
            n := n - 1; // Decrease n towards 0.
        }
    }
}