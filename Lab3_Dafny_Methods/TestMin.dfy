// Method that finds the smaller of two integers a and b.
method Min(a: int, b: int) returns (m: int)
    // Precondition: No specific requirements for inputs (true).
    requires true 
    // Postcondition: The returned value m satisfies one of the following:
    // m == a and a <= b (a is the smaller or equal value)
    // m == b and b <= a (b is the smaller or equal value)
    // m == a and m == b (both are equal)
    ensures (m == a && a <= b) || (m == b && b <= a) || (m == a && m == b)
{ 
    if a < b {
        // If a is less than b, set m to a.
        m := a;
    } else {
        // Otherwise, set m to b.
        m := b;
    }
}

// A test method to verify that the Max method works correctly.
method {:test} TestMin()
{
    // Test case 1: Min(2, 3) should return 2.
    var x := Min(2, 3);
    assert x == 2;

    // Test case 2: Min(-4, 1) should return -4.
    var y := Min(-4, 1);
    assert y == -4;

    // Test case 3: Min(0, 0) should return 0, since both values are the same.
    var z := Min(0, 0);
    assert z == 0;
}