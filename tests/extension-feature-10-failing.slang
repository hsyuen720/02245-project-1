// Extension Feature 10: early return (★★)
// This test should fail because the postcondition is not satisfied

method bad_return(x: Int): Int
    requires x >= 0
    // @CheckError
    ensures result > 0  // This should fail when x == 0
{
    match {
        x == 0 => 
            return 0,  // Returns 0, but ensures says result > 0
        true =>
            return x + 1
    }
}

method missing_return_value(x: Int): Int
    requires x >= 0
    ensures result >= 0
{
    match {
        x == 0 =>
            return 1,
        x == 1 =>
            return 2,
        true =>
            var y: Int := x + 1;
            // @CheckError
            assert y < 0  // This should fail
    }
    // Missing return on the last branch - but the assert should fail first
}
