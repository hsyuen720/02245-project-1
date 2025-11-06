// Extension Feature 11: Continue in loops
// This test demonstrates continue statement skipping even numbers

method sumOdd(n: Int): Int
    requires n >= 0
    ensures result >= 0
{
    var i: Int := 0;
    var sum: Int := 0;
    loop
        invariant i >= 0
        invariant i <= n
        invariant sum >= 0
    {
        i < n =>
            i := i + 1;
            match {
                i % 2 == 0 => continue  // Skip even numbers
            };
            sum := sum + i
    };
    return sum
}
