function Fib(n: nat): nat
{
    // Recursive definition of the Fibonacci sequence
    if n < 2 then n else Fib(n - 1) + Fib(n - 2)
}

method FibIter(n: nat) returns (x: nat)
    ensures x == Fib(n) // Ensures the output matches the Fibonacci function
{
    if n == 0 { // Base case for Fib(0)
        return 0;
    }
    if n == 1 { // Base case for Fib(1)
        return 1;
    }

    var a: nat := 0; // a holds Fib(i-2)
    var b: nat := 1; // b holds Fib(i-1)
    var i: nat := 2; // Start loop from i=2 as we handle 0 and 1 separately

    while i <= n
        invariant 2 <= i <= n + 1 // Loop invariant ensuring valid range of i
        invariant a == Fib(i - 2) && b == Fib(i - 1) // Ensures a and b hold correct Fibonacci values
    {
        var temp := a + b; // Calculate the next Fibonacci number
        a := b; // Shift a and b forward in the sequence
        b := temp;
        i := i + 1; // Increment i to move to the next Fibonacci number
    }
    x := b; // Final result is stored in b
}
