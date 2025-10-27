method clientFail(n: Int): Int
    requires n >= 2
    ensures result == n * (n + 1) / 2
{
    var acc: Int := 0;
    for i in 1..(n + 1)
        // @CheckError - Wrong invariant formula
        invariant acc == i * i
        invariant i >= 1 && i <= n + 1
    {
        acc := acc + i
    };
    return acc
}
