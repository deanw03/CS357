// Function to compute 2^n for any non-negative integer n
function pow2(n: nat): nat
{
    if n == 0 then
        1  // Base case: 2^0 = 1
    else
        2 * pow2(n - 1)  // Recursive case: 2^n = 2 * 2^(n-1)
}
// Generalized function to compute a^n for any integer a and non-negative integer n
function pow(a: int, n: nat): int
{
    if n == 0 then
        1  // Base case: a^0 = 1 for any a
    else
        a * pow(a, n - 1)  // Recursive case: a^n = a * a^(n-1)
}
