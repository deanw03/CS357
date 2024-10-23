// Function definition from the previous question
function pow(a: int, n: nat): int
{
    if n == 0 then
        1
    else
        a * pow(a, n - 1)
}

// Method to compute a^n for any a ∈ Z and n ∈ N using iteration.
method Pow(a: int, n: nat) returns (result: int)
    // Postcondition: The result should match the function pow(a, n).
    ensures result == pow(a, n)
{
    result := 1;  // Start with result as 1 (a^0)
    var i := 0;   // Start i at 0

    // Loop to compute a^n iteratively
    while i < n
        invariant 0 <= i <= n  // Loop invariant: i is within bounds
        invariant result == pow(a, i)  // Result matches a^i at each step
    {
        result := result * a;  // Multiply result by a at each iteration
        i := i + 1;  // Increment the loop counter
    }
}
