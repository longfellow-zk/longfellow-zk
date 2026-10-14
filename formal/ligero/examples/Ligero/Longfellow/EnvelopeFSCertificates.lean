import examples.Ligero.Longfellow.EnvelopeFS
import examples.Ligero.Longfellow.OptimizedIOPCertificates

/-! All v7/v8 scalar FS certificates. The exponent is the IOP coefficient;
FS error additionally pays the proved linear query factor and Merkle binding. -/
namespace Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized

variable {AlphaKey Salt Digest Encoding Output PrefixOut RunOut : Type*}
variable [DecidableEq AlphaKey] [Inhabited Salt] [Inhabited Digest]
variable [Fintype Digest] [DecidableEq Digest] [DecidableEq Encoding]
variable {N merkleT prefixFuel runFuel : ℕ}

abbrev v7Sig_v2_fs_localBound := @CertifiedResult.v2_fs_localBound v7Sig_v2_certified rfl

def v7Sig_v2_fs_extraction :=
  @CertifiedResult.v2_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Sig_v2_certified rfl

def v7Sig_v2_fs_soundness :=
  @CertifiedResult.v2_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Sig_v2_certified rfl

abbrev v7Sig_v3_fs_localBound := @CertifiedResult.v3_fs_localBound v7Sig_v3_certified rfl

def v7Sig_v3_fs_extraction :=
  @CertifiedResult.v3_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Sig_v3_certified rfl

def v7Sig_v3_fs_soundness :=
  @CertifiedResult.v3_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Sig_v3_certified rfl

abbrev v7Sig_v1_fs_localBound := @CertifiedResult.v1_fs_localBound v7Sig_v1_certified rfl

def v7Sig_v1_fs_extraction :=
  @CertifiedResult.v1_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Sig_v1_certified rfl

def v7Sig_v1_fs_soundness :=
  @CertifiedResult.v1_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Sig_v1_certified rfl

abbrev v7Hash1_v2_fs_localBound := @CertifiedResult.v2_fs_localBound v7Hash1_v2_certified rfl

def v7Hash1_v2_fs_extraction :=
  @CertifiedResult.v2_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash1_v2_certified rfl

def v7Hash1_v2_fs_soundness :=
  @CertifiedResult.v2_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash1_v2_certified rfl

abbrev v7Hash1_v3_fs_localBound := @CertifiedResult.v3_fs_localBound v7Hash1_v3_certified rfl

def v7Hash1_v3_fs_extraction :=
  @CertifiedResult.v3_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash1_v3_certified rfl

def v7Hash1_v3_fs_soundness :=
  @CertifiedResult.v3_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash1_v3_certified rfl

abbrev v7Hash1_v1_fs_localBound := @CertifiedResult.v1_fs_localBound v7Hash1_v1_certified rfl

def v7Hash1_v1_fs_extraction :=
  @CertifiedResult.v1_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash1_v1_certified rfl

def v7Hash1_v1_fs_soundness :=
  @CertifiedResult.v1_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash1_v1_certified rfl

abbrev v7Hash2_v2_fs_localBound := @CertifiedResult.v2_fs_localBound v7Hash2_v2_certified rfl

def v7Hash2_v2_fs_extraction :=
  @CertifiedResult.v2_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash2_v2_certified rfl

def v7Hash2_v2_fs_soundness :=
  @CertifiedResult.v2_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash2_v2_certified rfl

abbrev v7Hash2_v3_fs_localBound := @CertifiedResult.v3_fs_localBound v7Hash2_v3_certified rfl

def v7Hash2_v3_fs_extraction :=
  @CertifiedResult.v3_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash2_v3_certified rfl

def v7Hash2_v3_fs_soundness :=
  @CertifiedResult.v3_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash2_v3_certified rfl

abbrev v7Hash2_v1_fs_localBound := @CertifiedResult.v1_fs_localBound v7Hash2_v1_certified rfl

def v7Hash2_v1_fs_extraction :=
  @CertifiedResult.v1_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash2_v1_certified rfl

def v7Hash2_v1_fs_soundness :=
  @CertifiedResult.v1_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash2_v1_certified rfl

abbrev v7Hash3_v2_fs_localBound := @CertifiedResult.v2_fs_localBound v7Hash3_v2_certified rfl

def v7Hash3_v2_fs_extraction :=
  @CertifiedResult.v2_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash3_v2_certified rfl

def v7Hash3_v2_fs_soundness :=
  @CertifiedResult.v2_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash3_v2_certified rfl

abbrev v7Hash3_v3_fs_localBound := @CertifiedResult.v3_fs_localBound v7Hash3_v3_certified rfl

def v7Hash3_v3_fs_extraction :=
  @CertifiedResult.v3_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash3_v3_certified rfl

def v7Hash3_v3_fs_soundness :=
  @CertifiedResult.v3_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash3_v3_certified rfl

abbrev v7Hash3_v1_fs_localBound := @CertifiedResult.v1_fs_localBound v7Hash3_v1_certified rfl

def v7Hash3_v1_fs_extraction :=
  @CertifiedResult.v1_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash3_v1_certified rfl

def v7Hash3_v1_fs_soundness :=
  @CertifiedResult.v1_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash3_v1_certified rfl

abbrev v7Hash4_v2_fs_localBound := @CertifiedResult.v2_fs_localBound v7Hash4_v2_certified rfl

def v7Hash4_v2_fs_extraction :=
  @CertifiedResult.v2_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash4_v2_certified rfl

def v7Hash4_v2_fs_soundness :=
  @CertifiedResult.v2_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash4_v2_certified rfl

abbrev v7Hash4_v3_fs_localBound := @CertifiedResult.v3_fs_localBound v7Hash4_v3_certified rfl

def v7Hash4_v3_fs_extraction :=
  @CertifiedResult.v3_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash4_v3_certified rfl

def v7Hash4_v3_fs_soundness :=
  @CertifiedResult.v3_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash4_v3_certified rfl

abbrev v7Hash4_v1_fs_localBound := @CertifiedResult.v1_fs_localBound v7Hash4_v1_certified rfl

def v7Hash4_v1_fs_extraction :=
  @CertifiedResult.v1_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash4_v1_certified rfl

def v7Hash4_v1_fs_soundness :=
  @CertifiedResult.v1_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v7Hash4_v1_certified rfl

abbrev v8Sig_v2_fs_localBound := @CertifiedResult.v2_fs_localBound v8Sig_v2_certified rfl

def v8Sig_v2_fs_extraction :=
  @CertifiedResult.v2_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Sig_v2_certified rfl

def v8Sig_v2_fs_soundness :=
  @CertifiedResult.v2_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Sig_v2_certified rfl

abbrev v8Sig_v3_fs_localBound := @CertifiedResult.v3_fs_localBound v8Sig_v3_certified rfl

def v8Sig_v3_fs_extraction :=
  @CertifiedResult.v3_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Sig_v3_certified rfl

def v8Sig_v3_fs_soundness :=
  @CertifiedResult.v3_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Sig_v3_certified rfl

abbrev v8Sig_v1_fs_localBound := @CertifiedResult.v1_fs_localBound v8Sig_v1_certified rfl

def v8Sig_v1_fs_extraction :=
  @CertifiedResult.v1_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Sig_v1_certified rfl

def v8Sig_v1_fs_soundness :=
  @CertifiedResult.v1_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Sig_v1_certified rfl

abbrev v8Hash1_v2_fs_localBound := @CertifiedResult.v2_fs_localBound v8Hash1_v2_certified rfl

def v8Hash1_v2_fs_extraction :=
  @CertifiedResult.v2_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash1_v2_certified rfl

def v8Hash1_v2_fs_soundness :=
  @CertifiedResult.v2_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash1_v2_certified rfl

abbrev v8Hash1_v3_fs_localBound := @CertifiedResult.v3_fs_localBound v8Hash1_v3_certified rfl

def v8Hash1_v3_fs_extraction :=
  @CertifiedResult.v3_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash1_v3_certified rfl

def v8Hash1_v3_fs_soundness :=
  @CertifiedResult.v3_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash1_v3_certified rfl

abbrev v8Hash1_v1_fs_localBound := @CertifiedResult.v1_fs_localBound v8Hash1_v1_certified rfl

def v8Hash1_v1_fs_extraction :=
  @CertifiedResult.v1_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash1_v1_certified rfl

def v8Hash1_v1_fs_soundness :=
  @CertifiedResult.v1_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash1_v1_certified rfl

abbrev v8Hash2_v2_fs_localBound := @CertifiedResult.v2_fs_localBound v8Hash2_v2_certified rfl

def v8Hash2_v2_fs_extraction :=
  @CertifiedResult.v2_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash2_v2_certified rfl

def v8Hash2_v2_fs_soundness :=
  @CertifiedResult.v2_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash2_v2_certified rfl

abbrev v8Hash2_v3_fs_localBound := @CertifiedResult.v3_fs_localBound v8Hash2_v3_certified rfl

def v8Hash2_v3_fs_extraction :=
  @CertifiedResult.v3_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash2_v3_certified rfl

def v8Hash2_v3_fs_soundness :=
  @CertifiedResult.v3_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash2_v3_certified rfl

abbrev v8Hash2_v1_fs_localBound := @CertifiedResult.v1_fs_localBound v8Hash2_v1_certified rfl

def v8Hash2_v1_fs_extraction :=
  @CertifiedResult.v1_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash2_v1_certified rfl

def v8Hash2_v1_fs_soundness :=
  @CertifiedResult.v1_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash2_v1_certified rfl

abbrev v8Hash3_v2_fs_localBound := @CertifiedResult.v2_fs_localBound v8Hash3_v2_certified rfl

def v8Hash3_v2_fs_extraction :=
  @CertifiedResult.v2_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash3_v2_certified rfl

def v8Hash3_v2_fs_soundness :=
  @CertifiedResult.v2_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash3_v2_certified rfl

abbrev v8Hash3_v3_fs_localBound := @CertifiedResult.v3_fs_localBound v8Hash3_v3_certified rfl

def v8Hash3_v3_fs_extraction :=
  @CertifiedResult.v3_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash3_v3_certified rfl

def v8Hash3_v3_fs_soundness :=
  @CertifiedResult.v3_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash3_v3_certified rfl

abbrev v8Hash3_v1_fs_localBound := @CertifiedResult.v1_fs_localBound v8Hash3_v1_certified rfl

def v8Hash3_v1_fs_extraction :=
  @CertifiedResult.v1_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash3_v1_certified rfl

def v8Hash3_v1_fs_soundness :=
  @CertifiedResult.v1_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash3_v1_certified rfl

abbrev v8Hash4_v2_fs_localBound := @CertifiedResult.v2_fs_localBound v8Hash4_v2_certified rfl

def v8Hash4_v2_fs_extraction :=
  @CertifiedResult.v2_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash4_v2_certified rfl

def v8Hash4_v2_fs_soundness :=
  @CertifiedResult.v2_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash4_v2_certified rfl

abbrev v8Hash4_v3_fs_localBound := @CertifiedResult.v3_fs_localBound v8Hash4_v3_certified rfl

def v8Hash4_v3_fs_extraction :=
  @CertifiedResult.v3_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash4_v3_certified rfl

def v8Hash4_v3_fs_soundness :=
  @CertifiedResult.v3_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash4_v3_certified rfl

abbrev v8Hash4_v1_fs_localBound := @CertifiedResult.v1_fs_localBound v8Hash4_v1_certified rfl

def v8Hash4_v1_fs_extraction :=
  @CertifiedResult.v1_fs_extraction AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash4_v1_certified rfl

def v8Hash4_v1_fs_soundness :=
  @CertifiedResult.v1_fs_soundness AlphaKey Salt Digest Encoding Output PrefixOut RunOut
    _ _ _ _ _ _ N merkleT prefixFuel runFuel v8Hash4_v1_certified rfl

end Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized
