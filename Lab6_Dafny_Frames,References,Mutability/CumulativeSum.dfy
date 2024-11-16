function SumTo(a: array<int>, i: nat): int
    reads a  // Specifies that this function reads the array `a`
    requires 0 <= i <= a.Length  // Ensures the index `i` is within valid bounds
{
    if i == 0 then 0  // Base case: sum up to index 0 is 0
    else SumTo(a, i - 1) + a[i - 1]  // Recursive case: add the previous element to the sum
}

method CumulativeSum(a: array<int>)
    requires a.Length > 0  // Precondition: Array `a` must have at least one element
    modifies a  // Allows modifications to the array `a`
    ensures forall i :: 0 <= i < a.Length ==> a[i] == SumTo(a, i + 1)  // Postcondition: Each element becomes the cumulative sum up to its index
{
    var sum := 0;  // Initialize a variable to store the running cumulative sum

    for i := 0 to a.Length
        invariant 0 <= i <= a.Length  // Loop bounds invariant
        invariant sum == SumTo(a, i)  // Tracks the cumulative sum up to index `i`
        invariant forall j :: 0 <= j < i ==> a[j] == SumTo(a, j + 1)  // Ensures correctness of cumulative sum for processed indices
    {
        sum := sum + a[i];  // Update the running cumulative sum
        a[i] := sum;  // Store the cumulative sum in the array
    }
}
