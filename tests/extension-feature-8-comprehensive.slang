// Extension Feature 8: Total correctness of loops - comprehensive test
// Tests multiple aspects of loop termination checking

method countdown(n: Int): Int
    requires n >= 0
    ensures result == 0
{
    var i: Int := n;
    loop 
        invariant i >= 0
        decreases i
    {
        i > 0 =>
            i := i - 1
    };
    assert i == 0;
    
    return i
}

method div_by_two(n: Int): Int
    requires n >= 0
    ensures result >= 0
{
    var x: Int := n;
    loop 
        invariant x >= 0
        decreases x
    {
        x >= 2 =>
            x := x - 2
    };
    
    return x
}
