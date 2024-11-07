method Filter<T>(a: array<T>, P: T -> bool) returns (s: seq<T>)
    ensures forall i :: 0 <= i < |s| ==> P(s[i])  // All elements in s satisfy the predicate P
    ensures forall i :: 0 <= i < a.Length && P(a[i]) ==> a[i] in s  // All elements in a that satisfy P are in s
    ensures forall i :: 0 <= i < a.Length && !P(a[i]) ==> a[i] !in s  // Elements not satisfying P are not in s
{ 
    s := []; // Initialize s as an empty sequence
    var i := 0; // Start with the first index

    while i < a.Length
        invariant 0 <= i <= a.Length // i is within the bounds of a
        invariant forall j :: 0 <= j < |s| ==> P(s[j]) // All elements in s satisfy P
        invariant forall j :: 0 <= j < i && P(a[j]) ==> a[j] in s  // Elements that satisfy P up to i are in s
        invariant forall j :: 0 <= j < i && !P(a[j]) ==> a[j] !in s  // Elements that do not satisfy P up to i are not in s
    {
        if P(a[i]) { // If the element satisfies P,
            s := s + [a[i]]; // add it to the sequence s
        }
        i := i + 1; // Move to the next index
    }     
}
