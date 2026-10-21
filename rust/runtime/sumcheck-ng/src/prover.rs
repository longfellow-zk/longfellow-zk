// Copyright 2026 Google LLC.
// SPDX-License-Identifier: Apache-2.0

use crate::{
    dense::{as_scalar, bind},
    eq::{next_weights, weights},
    eval::EvaluatedLayer,
    proof::{LayerProof, SumcheckProof, SumcheckProofGeometry},
    transcript::{assertion_weights, begin, combine},
    verifier_data::{LayerVerifierData, RoundCoefficients, VerifierData},
    wiring::contract,
    LagrangeBasis, Poly, QuadRoundPoly, QuadWirePoly, TranscriptSumcheck,
};
use runtime_algebra::{ElementOf, InterpolationField, SupportsSampling};
use runtime_random::Transcript;

/// Bind the public statement, then prove the evaluated circuit.
pub fn prove<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    evaluated: Vec<EvaluatedLayer<ElementOf<F>>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, VerifierData<ElementOf<F>>) {
    let inputs = &evaluated
        .last()
        .expect("use prove_core for a zero-layer circuit")
        .inputs;
    transcript.write_sumcheck_statement(circuit, &inputs[..circuit.raw.npublic_input], f);
    prove_core(evaluated, pad, circuit, transcript, f)
}

/// Prove after the caller has bound the statement to the transcript.
pub fn prove_core<const W: usize, F: InterpolationField<W> + SupportsSampling<W>>(
    evaluated: Vec<EvaluatedLayer<ElementOf<F>>>,
    pad: &SumcheckProof<W, F>,
    circuit: &core_proto::circuit::Circuit<F>,
    transcript: &mut Transcript,
    f: &F,
) -> (SumcheckProof<W, F>, VerifierData<ElementOf<F>>) {
    pad.validate(&SumcheckProofGeometry::from_circuit(circuit))
        .expect("pad shape mismatch");
    assert_eq!(evaluated.len(), circuit.raw.layers.len());
    let mut lambda = begin(circuit, transcript, f);
    let mut claim = f.zero();
    let mut layers = Vec::with_capacity(evaluated.len());
    let mut verifier_layers = Vec::with_capacity(evaluated.len());
    let basis = LagrangeBasis::new(f);
    for (index, ((layer, layer_pad), layer_evaluation)) in circuit
        .raw
        .layers
        .iter()
        .zip(&pad.layers)
        .zip(evaluated)
        .enumerate()
    {
        let EvaluatedLayer {
            inputs,
            assertion_outputs,
        } = layer_evaluation;
        let assertions = {
            let outputs = assertion_outputs;
            assert_eq!(outputs.len(), lambda.len());
            assertion_weights(&outputs, index, transcript, f)
        };
        // Fold buffers live only in this scope, before the next public weights.
        let (endpoints, rounds, point, round_coefficients) = {
            let mut wires = inputs;
            assert!(wires.len() <= layer.nw().max(1));
            wires.resize(layer.nw().max(1), f.zero());
            let mut weights = contract(
                layer,
                &circuit.raw.constants,
                &lambda,
                &assertions,
                &wires,
                0,
                f,
            );
            let mut rounds = Vec::with_capacity(layer.logw());
            let mut point = Vec::with_capacity(layer.logw());
            let mut round_coefficients = Vec::with_capacity(layer.logw());
            for round_pad in &layer_pad.rounds {
                let polynomial = quad_round_poly(&weights, &wires, &claim, f);
                let round_values = polynomial.to_wire();
                let message = round_values.sub(round_pad, f);
                let challenge = transcript.round(&message, f);
                let coefficients = RoundCoefficients::new(&basis, &challenge, f);
                claim = coefficients.evaluate(&round_values, &claim, f);
                bind(&mut wires, &challenge, f);
                bind(&mut weights, &challenge, f);
                rounds.push(message);
                point.push(challenge);
                round_coefficients.push(coefficients);
            }
            (
                [as_scalar::<W, F>(&wires), as_scalar::<W, F>(&weights)],
                rounds,
                point,
                round_coefficients,
            )
        };
        assert_eq!(
            claim,
            f.mulf(&endpoints[0], &endpoints[1]),
            "single-hand terminal product mismatch"
        );
        let claims = std::array::from_fn(|i| f.subf(&endpoints[i], &layer_pad.claims[i]));
        let chi = weights(layer.logw(), layer.nw(), &point, f);
        let mu = contract(
            layer,
            &circuit.raw.constants,
            &lambda,
            &assertions,
            &chi,
            1,
            f,
        );
        let alpha = combine(&claims, transcript, f);
        claim = endpoints[0].clone();
        f.fma(&mut claim, &alpha, &endpoints[1]);
        lambda = next_weights(chi, &mu, &alpha, f);
        layers.push(LayerProof { rounds, claims });
        verifier_layers.push(LayerVerifierData {
            rounds: round_coefficients,
            alpha,
        });
    }
    (
        SumcheckProof { layers },
        VerifierData {
            layers: verifier_layers,
            input_weights: lambda,
        },
    )
}

/// Evaluates the quad round polynomial of degree 2 (represented
/// by 3 evaluation points) for the current sumcheck prover round.
///
/// Directly computes the evaluations [g(0), g(1), g(2)] without intermediate
/// monomial or Newton conversions.
#[inline]
fn quad_round_poly<const W: usize, F: InterpolationField<W>>(
    qw: &[ElementOf<F>],
    witness_values: &[ElementOf<F>],
    sum: &ElementOf<F>,
    f: &F,
) -> Poly<3, W, F> {
    assert_eq!(qw.len(), witness_values.len());
    let num_variables = qw.len();
    let num_pairs = num_variables / 2;
    let mut accum_a0 = f.zero_accum();
    let mut accum_a2 = f.zero_accum();

    for i in 0..num_pairs {
        let idx = 2 * i;
        f.mac(&mut accum_a0, &qw[idx], &witness_values[idx]);
        let dqw = f.subf(&qw[idx + 1], &qw[idx]);
        let dw = f.subf(&witness_values[idx + 1], &witness_values[idx]);
        f.mac(&mut accum_a2, &dqw, &dw);
    }

    if !num_variables.is_multiple_of(2) {
        let last = num_variables - 1;
        f.mac(&mut accum_a0, &qw[last], &witness_values[last]);
        f.mac(&mut accum_a2, &qw[last], &witness_values[last]);
    }

    let a0 = f.accum_reduce(&accum_a0);
    let a2 = f.accum_reduce(&accum_a2);

    // g(0) = a0
    // g(1) = sum - a0
    let mut g1 = sum.clone();
    f.sub(&mut g1, &a0);

    // c1 = g(1) - a0 - a2 = sum - 2*a0 - a2
    let mut c1 = g1.clone();
    f.sub(&mut c1, &a0);
    f.sub(&mut c1, &a2);

    // Evaluate g(2) = a2*pt(2)^2 + c1*pt(2) + a0 using Horner's method for binary field
    // compatibility:
    let pt2 = f.poly_evaluation_point(2);
    let mut g2 = a2.clone();
    f.mul(&mut g2, &pt2);
    f.add(&mut g2, &c1);
    f.mul(&mut g2, &pt2);
    f.add(&mut g2, &a0);

    Poly {
        evaluations: [a0, g1, g2],
    }
}
