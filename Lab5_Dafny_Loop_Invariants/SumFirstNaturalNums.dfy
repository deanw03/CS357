method SumFirst(n: nat) returns (sum: nat)
    ensures sum == n * (n + 1) / 2  // Ensures the result matches the formula for the sum of the first n natural numbers
{
    sum := 0;  // Initialize the sum to 0
    var i := 0; // Initialize the counter i to 0

    while i <= n
        invariant 0 <= i <= n + 1  // Invariant: i is within the expected bounds
        invariant sum == i * (i - 1) / 2 // Invariant: sum matches the expected value for the first i numbers
    {
        sum := sum + i; // Add the current value of i to the sum
        i := i + 1;     // Increment i to move to the next number
    }
}
