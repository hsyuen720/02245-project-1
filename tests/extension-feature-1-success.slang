method client() {
    var acc: Int := 0;
    for i in 0..10 {
        acc := acc + i
    };
    assert acc == 9 * 10 / 2
}
