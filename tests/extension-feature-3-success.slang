// Extension Feature 3: Efficient assignments via DSA
// This test verifies that assignments are handled correctly through DSA transformation

method test(): Int
    ensures result == 15
{
    var x: Int := 5;
    var y: Int := 10;
    var z: Int;
    
    z := x + y;
    
    return z
}
