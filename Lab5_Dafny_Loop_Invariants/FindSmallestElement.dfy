method Smallest(a: array<int>) returns (minIndex: nat)
    requires a.Length > 0 // Array must have at least one element
    ensures 0 <= minIndex < a.Length // minIndex is a valid index within the array
    ensures forall i :: 0 <= i < a.Length ==> a[minIndex] <= a[i]  // Ensures minIndex points to the smallest element
{
    minIndex := 0; // Start with the first element as the minimum
    var minValue := a[0]; // Set the initial minimum value

    for i := 1 to a.Length // Loop through the array starting from the second element
        invariant 0 <= minIndex < a.Length // minIndex remains a valid index
        invariant minValue == a[minIndex] // minValue corresponds to a[minIndex]
        invariant forall j :: 0 <= j < i ==> a[minIndex] <= a[j]  // Elements before i are at least as large as a[minIndex]
    {
        if a[i] < minValue { // If a smaller element is found
            minValue := a[i]; // Update minValue to this new smallest value
            minIndex := i; // Update minIndex to point to the new smallest element
        }
    }
}
