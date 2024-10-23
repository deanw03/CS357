// Function definition for MaxDef, returns the greater of two values.
function MaxDef(a: int, b: int): int
{
    if a > b then a else b
}

// Method that returns the maximum of two integers a and b.
method Max(a: int, b: int) returns (m: int)
    // Ensures the returned value m matches the definition in MaxDef.
    ensures m == MaxDef(a, b)
{
    if a > b {
        m := a;
    } else {
        m := b;
    }
}
// Function definition for MinDef, returns the smaller of two values.
function MinDef(a: int, b: int): int
{
    if a < b then a else b
}

// Method that returns the minimum of two integers a and b.
method Min(a: int, b: int) returns (m: int)
    // Ensures the returned value m matches the definition in MinDef.
    ensures m == MinDef(a, b)
{
    if a < b {
        m := a;
    } else {
        m := b;
    }
}
