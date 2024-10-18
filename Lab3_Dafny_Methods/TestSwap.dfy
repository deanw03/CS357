// Method to swap the values of two elements in an array.
method swap(a: array<int>, i: nat, j: nat)
    // Indicates that the array `a` will be modified by this method.
    modifies a

    // Preconditions: i and j must be valid indices in the array.
    requires i < a.Length
    requires j < a.Length

    // Postconditions: After the swap, a[i] will hold the old value of a[j] and vice versa.
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])
{
    // Store the value at index i in a temporary variable.
    var temp := a[i];

    // Set a[i] to the value at index j.
    a[i] := a[j];

    // Set a[j] to the value stored in temp (the old value of a[i]).
    a[j] := temp;
}

// Test method to verify the swap function.
method {:main} TestSwap()
{
    // Create an array with values [1, 2, 3, 4].
    var a := new int[] [1, 2, 3, 4];

    // Assert the initial values at indices 1 and 3 are 2 and 4, respectively.
    assert a[1] == 2 && a[3] == 4;

    // Call the swap method to swap the values at indices 1 and 3.
    swap(a, 1, 3);

    // Assert that after swapping, the values at indices 1 and 3 have been exchanged.
    assert a[1] == 4 && a[3] == 2;
}
