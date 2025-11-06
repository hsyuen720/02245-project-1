// Extension Feature 9: global variables - demonstration test
// Shows working support for global variables, modifies clauses, and method calls

global counter: Int

method inc()
    modifies counter
    ensures counter == 5  // Fixed postcondition
{
    counter := 5
}

method client() 
    modifies counter
{
    counter := 0;
    
    assert counter == 0;
    inc();
    assert counter == 5;
    inc();
    assert counter == 5
}
