// Simple function with body and specification
function abs(x: Int): Int 
    ensures result >= 0
{
    x >= 0 ? x : -x
}

// Recursive function - specification trusted when used
function fac(n: Int): Int 
    requires n >= 0
    ensures result > 0
{
    n == 0 ? 1 : n * fac(n - 1)
}

method client() {
    // When functions are used in methods, we check preconditions
    // and assume postconditions hold
    var a: Int := abs(-5);
    assert a >= 0;
    
    var f: Int := fac(0);
    assert f > 0
}
