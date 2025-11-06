// Extension Feature 11: Breaking loops
// This test should verify successfully

method client(): Int
{
    var i: Int := 0;
    loop 
        invariant i >= 0
        invariant i <= 15
        invariant broke ==> i == 15
    { 
        true => 
            i := i + 1;
            match { 
                i == 15 => 
                    // The loop is interrupted. Execution resumes
                    // from the first line after the loop.
                    break 
            }
    };

    assert i == 15;
    return i
}
