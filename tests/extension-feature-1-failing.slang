method clientFail() {
    var acc: Int := 0;
    for i in 0..10 {
        acc := acc + i
    };
    // @CheckError
    assert acc == 100
}
