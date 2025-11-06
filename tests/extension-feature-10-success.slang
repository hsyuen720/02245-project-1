// Extension Feature 10: early return (★★)
// This test verifies that early returns work correctly and code after return is unreachable

method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1)/2
    decreases n
{
    match {
        n == 0 => 
            return 0,
        true => 
            var res: Int;
            res := sumn(n - 1);
            return res + n
    };
    assert false // not reachable, should pass
}

method early_return_in_branch(x: Int): Int
    ensures result >= 0
{
    match {
        x < 0 => 
            return 0,
        x == 0 =>
            return 1,
        true =>
            return x
    };
    // This code is unreachable since all branches return
    assert false
}

method multiple_returns(n: Int): Int
    requires n >= 0
{
    var i: Int := 0;
    loop 
        invariant i >= 0
        invariant i <= n + 1
    {
        i < n => 
            i := i + 1,
        true =>
            return i
    };
    // Unreachable - loop always returns
    assert false
}
