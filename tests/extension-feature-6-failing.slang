// Extension Feature 6: Functions with bodies - failing test
// This test should fail because the assertion cannot be proven using the function's postcondition

function abs(x: Int): Int 
    ensures result >= 0
{
    x >= 0 ? x : -x
}

function fac(n: Int): Int 
    requires n >= 0
    ensures result > 0
{
    n == 0 ? 1 : n * fac(n - 1)
}

method client(x: Int) 
    requires x < 0
{
    var a: Int := abs(x);
    // Even though we know a >= 0 from the postcondition,
    // we cannot prove that a == -x because the postcondition doesn't tell us that
    // @CheckError
    assert a == x  // This should fail because x < 0 but a >= 0
}

