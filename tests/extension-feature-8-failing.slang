// Extension Feature 8: Total correctness of loops
// This test should fail because the decreases clause doesn't strictly decrease

method infinite_loop(n: Int): Int
    requires n >= 0
{
    var i: Int := 0;
    loop 
        invariant i >= 0
        invariant i <= n + 1
        // @CheckError
        decreases n - i  // This doesn't strictly decrease because i stays at n
    {
        i < n =>
            i := i + 1,
        i == n =>
            // This branch doesn't change i, so decreases clause is not satisfied
            i := i
    };
    
    return i
}
