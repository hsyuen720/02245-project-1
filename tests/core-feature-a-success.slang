method m(x: Int) {
    var y: Int := x + 15;
    match {
      x > 0 => 
        assert y/x > 0,
      true => 
        y := 5
    };
    assert y > 0
}
