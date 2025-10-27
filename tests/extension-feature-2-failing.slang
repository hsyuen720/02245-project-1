// Extension Feature 2: verification of mutually recursive methods
// This test should fail - recursive method with incorrect postcondition

method sumn(n: Int): Int
    requires n >= 0
    // @CheckError
    ensures result == n * n  // Wrong postcondition!
{
    match {
        n == 0 => 
            return 0,
        n > 0 => 
            var res: Int;
            res := sumn(n - 1);
            return res + n
    }
}
