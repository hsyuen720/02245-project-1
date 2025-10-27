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
