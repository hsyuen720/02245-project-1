method sumn(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1)/2
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
