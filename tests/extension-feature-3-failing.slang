// Extension Feature 3: Efficient assignments - failing case  
// This test should fail because the postcondition is wrong

method test(): Int
    // @CheckError
    ensures result == 10  // Wrong: should be 15
{
    var x: Int := 5;
    var y: Int := 10;
    var z: Int;
    
    z := x + y;
    
    return z
}
