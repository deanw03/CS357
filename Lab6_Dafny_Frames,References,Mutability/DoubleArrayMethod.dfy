method DoubleArray(s: array<int>, t: array<int>)
    modifies t  // Allows modification of the array `t`
    requires s.Length == t.Length  // Precondition: `s` and `t` must have the same length
    ensures forall i :: 0 <= i < s.Length ==> t[i] == 2 * s[i]  // Postcondition: Every element in `t` is double the corresponding element in `s`
{
    for i := 0 to s.Length
        invariant 0 <= i <= s.Length  // Loop bounds invariant
        invariant forall j :: 0 <= j < i ==> t[j] == 2 * s[j]  // Invariant: Elements of `t` up to `i` are correctly doubled
    {
        t[i] := 2 * s[i];  // Double the value from `s` and store it in `t`
    }
}
