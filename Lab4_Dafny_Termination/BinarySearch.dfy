// Predicate to check if the array is sorted in non-decreasing order.
predicate sorted(a: array<int>)
    reads a
{
    // The array is sorted if for all i, j with 0 <= i < j < a.Length, a[i] <= a[j].
    forall i, j | 0 <= i < j < a.Length :: a[i] <= a[j]
}

// Method to perform binary search on a sorted array.
method BinarySearch(a: array<int>, value: int) returns (index: int)
    requires sorted(a)  // Precondition: array must be sorted.
    ensures index == -1 || 0 <= index < a.Length  // Index is valid or -1 if not found.
    ensures index == -1 ==> value !in a[..]  // If index is -1, value is not in the array.
    ensures index >= 0  ==> a[index] == value  // If index is valid, a[index] == value.
{
    var low := 0;  // Starting index.
    var high := a.Length;  // Ending index.

    // Continue searching while the range is valid.
    while low < high
        invariant 0 <= low <= high <= a.Length  // Indices are within bounds.
        invariant value !in a[..low] && value !in a[high..]  // Value not in excluded ranges.
    {
        var mid := (high + low) / 2;  // Middle index.

        if a[mid] < value {
            low := mid + 1;  // Search right half.
        } else if a[mid] > value {
            high := mid;  // Search left half.
        } else {
            return mid;  // Value found at mid.
        }
    }
    index := -1;  // Value not found.
}

