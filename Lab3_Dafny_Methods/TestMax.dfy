// Method that finds the larger of two integers a and b.
method Max(a: int, b: int) returns (m: int)
    // Precondition: No specific requirements for inputs (true).
    requires true
    // Postcondition: The returned value m satisfies one of the following:
    // m == a and a >= b (a is the larger or equal value)
    // m == b and b >= a (b is the larger or equal value)
    // m == a and m == b (both are equal)
    ensures (m == a && a >= b) || (m == b && b >= a) || (m == a && m == b)
{
    if a > b {
        // If a is greater than b, set m to a.
        m := a;
    } else {
        // Otherwise, set m to b.
        m := b;
    }
}

// A test method to verify that the Max method works correctly.
method {:test} TestMax()
{
    // Test case 1: Max(2, 3) should return 3.
    var x := Max(2, 3);
    assert x == 3;

    // Test case 2: Max(-4, 1) should return 1.
    var y := Max(-4, 1);
    assert y == 1;

    // Test case 3: Max(0, 0) should return 0, since both values are the same.
    var z := Max(0, 0);
    assert z == 0;
}

