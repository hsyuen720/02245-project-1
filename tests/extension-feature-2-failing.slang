method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * n
{
    match {
        n == 0 => 
            return 0,
        n > 0 => 
            var res: Int;
            // @CheckError
            res := sumn(n - 1);
            return res + n
    }
}
