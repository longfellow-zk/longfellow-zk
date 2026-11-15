// Copyright 2026 Google LLC. SPDX-License-Identifier: Apache-2.0
use super::{AdviceNode, BooleanAdvice};

#[test]
fn packed_advice_preserves_lanes_and_input_prefix() {
    let advice = BooleanAdvice::new(
        2,
        vec![
            AdviceNode::Input(0),
            AdviceNode::Input(1),
            AdviceNode::And(0, 1),
            AdviceNode::Xor(vec![0, 1, 2], true),
        ],
        vec![2, 3],
    )
    .unwrap();
    let a = 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaau128;
    let b = 0xccccccccccccccccccccccccccccccccu128;
    assert_eq!(
        advice.evaluate(&[a, b]).unwrap(),
        [a, b, a & b, !(a ^ b ^ (a & b))]
    );
    assert!(advice.evaluate(&[a]).is_err());
}

#[test]
fn malformed_advice_is_rejected_before_evaluation() {
    assert!(BooleanAdvice::new(1, vec![AdviceNode::Input(1)], vec![]).is_err());
    assert!(BooleanAdvice::new(1, vec![AdviceNode::And(0, 0)], vec![]).is_err());
    assert!(BooleanAdvice::new(1, vec![AdviceNode::Xor(vec![1], false)], vec![]).is_err());
    assert!(BooleanAdvice::new(1, vec![AdviceNode::Input(0)], vec![1]).is_err());
}
