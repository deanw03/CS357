// Function to compute the greatest common divisor (GCD) of two natural numbers a and b.
function gcd(a: int, b: int): int
    // Precondition: a and b must be greater than 0.
    requires a > 0 && b > 0
    // Decreases clause: the sum of a and b strictly decreases.
    decreases a + b  
{
    // If a equals b, return a (or b).
    if a == b then
        a
    // If b is greater than a, recursively call gcd with (b - a, a).
    else if b > a then
        gcd(b - a, a)
    // If a is greater than b, recursively call gcd with (b, a - b).
    else
        gcd(b, a - b)
}

