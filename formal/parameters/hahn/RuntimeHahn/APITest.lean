import RuntimeHahn.Hash
import RuntimeHahn.Signature
import RuntimeHahn.LigeroV7Sig
import RuntimeHahn.LigeroV7Hash1
import RuntimeHahn.LigeroV7Hash2
import RuntimeHahn.LigeroV7Hash3
import RuntimeHahn.LigeroV7Hash4
import RuntimeHahn.LigeroV7SigFS
import polygero.Benchmarks.HahnRateSixteenth.Certificates

/-! Reject corrupt proposals and audit every retained Hahn certificate's axioms. -/

open CodingTheory.HahnDelsarte.Fast.Integral

example : weightsCheck 6 2 1 2 [2, -4] = true := by decide +kernel
example : weightsCheck 6 2 1 2 [2, -3] = false := by decide +kernel
example : check 6 2 1 [2, -4] 2 [-6, 9] 1 = true := by decide +kernel
example : check 6 2 1 [2, -4] 2 [-6, 8] 1 = false := by decide +kernel

open Lean Elab Command
run_cmd do
  for endpoint in #[
      ``CodingTheory.HahnDelsarte.Fast.Integral.kernel_eq_eval,
      ``CodingTheory.HahnDelsarte.Fast.certificate_of_integral,
      ``RuntimeHahn.Hash.certificate_valid, ``RuntimeHahn.Hash.count_eq,
      ``RuntimeHahn.Signature.certificate_valid, ``RuntimeHahn.Signature.count_eq,
      ``RuntimeHahn.LigeroV7Sig.certificate_valid, ``RuntimeHahn.LigeroV7Sig.count_eq,
      ``RuntimeHahn.LigeroV7Hash1.certificate_valid, ``RuntimeHahn.LigeroV7Hash1.count_eq,
      ``RuntimeHahn.LigeroV7Hash2.certificate_valid, ``RuntimeHahn.LigeroV7Hash2.count_eq,
      ``RuntimeHahn.LigeroV7Hash3.certificate_valid, ``RuntimeHahn.LigeroV7Hash3.count_eq,
      ``RuntimeHahn.LigeroV7Hash4.certificate_valid, ``RuntimeHahn.LigeroV7Hash4.count_eq,
      ``RuntimeHahn.LigeroV7SigFS.certificate_valid, ``RuntimeHahn.LigeroV7SigFS.count_eq,
      ``RecursivePolygero.Benchmarks.HahnRateSixteenth.valid2152,
      ``RecursivePolygero.Benchmarks.HahnRateSixteenth.bound2152,
      ``RecursivePolygero.Benchmarks.HahnRateSixteenth.valid2140,
      ``RecursivePolygero.Benchmarks.HahnRateSixteenth.bound2140,
      ``RecursivePolygero.Benchmarks.HahnRateSixteenth.valid2129,
      ``RecursivePolygero.Benchmarks.HahnRateSixteenth.bound2129,
      ``RecursivePolygero.Benchmarks.HahnRateSixteenth.valid2119,
      ``RecursivePolygero.Benchmarks.HahnRateSixteenth.bound2119,
      ``RecursivePolygero.Benchmarks.HahnRateSixteenth.valid2109,
      ``RecursivePolygero.Benchmarks.HahnRateSixteenth.bound2109] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in Hahn certificate {endpoint}: {ax}"
