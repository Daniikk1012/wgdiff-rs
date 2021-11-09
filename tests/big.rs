use rand::prelude::*;
use wgdiff::{Diff, Patch};

fn bytes(length: usize) {
    let mut old = vec![0; length];
    let mut new = vec![0; length];

    let mut rng = SmallRng::from_entropy();
    rng.fill_bytes(&mut old);
    rng.fill_bytes(&mut new);

    old.patch(new.diff(&old));
    assert_eq!(old, new);
}

#[test]
#[ignore]
fn bytes_1_000() {
    bytes(1_000);
}

#[test]
#[ignore]
fn bytes_5_000() {
    bytes(5_000);
}

#[test]
#[ignore]
fn bytes_10_000() {
    bytes(10_000);
}
