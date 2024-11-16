class Pointer {
    var a: array<int>  // Variable to hold a reference to an integer array

    method InitArray(size: nat)
        modifies this  // Allows modification of the current object's state
    {
        var b := new int[size];  // Create a new array of integers with the given size
        a := b;  // Assign the new array to the field `a`
    }
}
