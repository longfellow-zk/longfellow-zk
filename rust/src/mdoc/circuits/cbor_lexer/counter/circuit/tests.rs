#[test]
fn order_certificate_uses_a_prime_divisor() {
    const P: u128 = 6_700_417;
    assert_eq!(u128::MAX % P, 0);
    const { assert!(P > 1 << 17) };
    assert!((2..)
        .take_while(|d| d * d <= P)
        .all(|d| !P.is_multiple_of(d)));
}
