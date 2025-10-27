method client(n: Int): Int
    requires n >= 0
    ensures result == n * (n + 1) / 2
{
    var acc: Int := 0;
    for i in 1..(n + 1)
        invariant acc == (i - 1) * i / 2
        invariant i >= 1 && i <= n + 1
    {
        acc := acc + i
    };
    return acc
}
