method m(x: Int): Int 
    requires x >= 0
    // @CheckError
    ensures result >= 0
    ensures result == 3 * x 
{
    var acc: Int := 0;
    acc := x / 2;
    acc := acc * 6;
    
    return acc
}
