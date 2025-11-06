// Extension Feature 11: Breaking loops - failing case
// This test should fail because the invariant doesn't hold when we break

method client(): Int
{
    var i: Int := 0;
    loop
        // @CheckError 
        invariant i == 0
    { 
        true => 
            i := i + 1;
            match { 
                i == 15 => 
                    break
            }
    };

    return i
}
