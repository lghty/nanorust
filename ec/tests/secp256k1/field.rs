use ec::secp256k1::field::FieldElement;

use rand::{thread_rng, Rng};

fn random_element() -> FieldElement {
    let mut rand32 = [0u8; 32];
    let mut rng = thread_rng();
    rng.fill(&mut rand32);
    let mut fe = FieldElement::new();
    fe.set_b32(&rand32);
    fe
}

#[test]
fn magnitude() {
    let (mut fe, mut zero) = (random_element(), FieldElement::new());
    fe.normalize();

    zero.clear();
    zero.negate_assign();

    let n: u32 = thread_rng().gen_range(1..9);
    zero.mul_int_assign(n.saturating_sub(1));
    fe.add_assign(&zero);

    if cfg!(feature = "verify") {
        assert_eq!(fe.magnitude(), n as i32);
    }
}

#[test]
fn cmp() {
    let lo = FieldElement::from([0, 0, 0, 0, 0, 0, 0, 1]);
    let mi = FieldElement::from([0, 0, 0, 0, 0, 0, 1, 1]);
    let hi = FieldElement::from([0, 0, 0, 0, 0, 1, 0, 0]);

    assert_eq!(lo.cmp(&lo), 0);
    assert_eq!(lo.cmp(&hi), -1);
    assert_eq!(hi.cmp(&lo), 1);

    assert_eq!(mi.cmp(&hi), -1);
    assert_eq!(mi.cmp(&lo), 1);
}
