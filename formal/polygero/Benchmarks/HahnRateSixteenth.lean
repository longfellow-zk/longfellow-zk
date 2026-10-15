import polygero.Benchmarks.HahnRateSixteenth.Certificates
import polygero.Theorems.Soundness
namespace RecursivePolygero.Benchmarks.HahnRateSixteenth
private def q : ℕ := 2^128
private def ratio (m t : ℕ) : ℚ := ((m.choose t : ℕ) : ℚ) / (((8192).choose t : ℕ) : ℚ)
private def eta (t : ℕ) : ℚ := ratio 639 t
private def mu : ℚ := (((8192).choose 641 : ℕ) : ℚ) / ((q : ℚ)^65)
private def epsilon (θ : ℚ) : ℚ := θ + (1-θ)*(mu + 1/(q : ℚ))
private def paperTheta (t u : ℕ) : ℚ := max (ratio 1087 t) (DiscreteThreshold.candidate q u (eta t))
private def hahnTheta (t a : ℕ) : ℚ := ratio (a-1) t
/-- The five checked fixed-weight polynomial certificates used by this table. -/
inductive CertificateId
  | c2152 | c2140 | c2129 | c2119 | c2109

structure CertificateData where
  cutoff : ℕ
  listBound : ℕ
  coefficients : List ℕ

def certificateData : CertificateId → CertificateData
  | .c2152 => ⟨2152, 1190814368820024810156822069, coeffs2152⟩
  | .c2140 => ⟨2140, 575194250790913053427560994641, coeffs2140⟩
  | .c2129 => ⟨2129, 185306271434729699977480333368813, coeffs2129⟩
  | .c2119 => ⟨2119, 59986470006650195744778424732198221, coeffs2119⟩
  | .c2109 => ⟨2109, 32665022220779624182686981783224084145, coeffs2109⟩

structure Row where
  t : ℕ
  certificate : CertificateId
  u : ℕ
  paperBits : ℕ
  hahnBits : ℕ

def Row.a (r : Row) : ℕ := (certificateData r.certificate).cutoff
def Row.L (r : Row) : ℕ := (certificateData r.certificate).listBound

def rows : List Row := [
  ⟨50, .c2152, 27521976506, 93, 97⟩,
  ⟨51, .c2152, 7402385836, 95, 99⟩,
  ⟨52, .c2152, 1989397207, 97, 100⟩,
  ⟨53, .c2152, 534230098, 99, 102⟩,
  ⟨54, .c2152, 143347999, 100, 104⟩,
  ⟨55, .c2140, 38433570, 102, 107⟩,
  ⟨56, .c2140, 10296390, 104, 109⟩,
  ⟨57, .c2140, 2756219, 106, 111⟩,
  ⟨58, .c2140, 737219, 108, 113⟩,
  ⟨59, .c2140, 197030, 110, 115⟩,
  ⟨60, .c2129, 52616, 112, 117⟩,
  ⟨61, .c2129, 14040, 114, 119⟩,
  ⟨62, .c2129, 3743, 116, 121⟩,
  ⟨63, .c2129, 997, 118, 123⟩,
  ⟨64, .c2129, 265, 119, 125⟩,
  ⟨65, .c2119, 71, 121, 126⟩,
  ⟨66, .c2119, 19, 123, 127⟩,
  ⟨67, .c2119, 5, 125, 127⟩,
  ⟨68, .c2119, 1, 127, 127⟩,
  ⟨69, .c2119, 1, 127, 127⟩,
  ⟨70, .c2109, 1, 127, 127⟩]
def rowOk (r : Row) : Prop :=
  (50 ≤ r.t ∧ r.t ≤ 70) ∧
  (1088 ≤ r.a ∧ r.a ≤ 8192) ∧
  DiscreteThreshold.IsLeastIndex q (eta r.t) r.u ∧
  (1 ≤ min q r.L ∧ DiscreteThreshold.candidate (min q r.L) 1 (eta r.t) ≤ hahnTheta r.t r.a) ∧
  epsilon (paperTheta r.t r.u) ≤ (1 : ℚ)/(2^r.paperBits : ℕ) ∧
  (1 : ℚ)/(2^(r.paperBits+1) : ℕ) < epsilon (paperTheta r.t r.u) ∧
  epsilon (hahnTheta r.t r.a) ≤ (1 : ℚ)/(2^r.hahnBits : ℕ) ∧
  (1 : ℚ)/(2^(r.hahnBits+1) : ℕ) < epsilon (hahnTheta r.t r.a)
def rowOkBool (r : Row) : Bool :=
  letI : Decidable (rowOk r) := by unfold rowOk; infer_instance
  decide (rowOk r)
theorem allRowsBool : rows.all rowOkBool = true := by native_decide

theorem allRows (r : Row) (hr : r ∈ rows) : rowOk r := by
  have hb : rowOkBool r = true := (List.all_eq_true.mp allRowsBool) r hr
  unfold rowOkBool at hb
  simpa only [decide_eq_true_eq] using hb

private theorem certificateAt (id : CertificateId) :
    CodingTheory.HahnDelsarte.certificateValid 8192
      (certificateData id).cutoff 639 (certificateData id).coefficients = true ∧
    CodingTheory.HahnDelsarte.certifiedBound 8192
      (certificateData id).cutoff (certificateData id).coefficients =
      (certificateData id).listBound := by
  cases id <;> simp [certificateData, valid2152, bound2152, valid2140, bound2140,
    valid2129, bound2129, valid2119, bound2119, valid2109, bound2109]

theorem selectedCertificate (r : Row) :
    CodingTheory.HahnDelsarte.certificateValid 8192 r.a 639
      (certificateData r.certificate).coefficients = true ∧
    CodingTheory.HahnDelsarte.certifiedBound 8192 r.a
      (certificateData r.certificate).coefficients = r.L :=
  certificateAt r.certificate

/-- The table contains exactly one row for each query count in the benchmark. -/
theorem coverage (t : ℕ) (ht : 50 ≤ t ∧ t ≤ 70) :
    ∃ r, r ∈ rows ∧ r.t = t := by
  rcases ht with ⟨hlo, hhi⟩
  interval_cases t <;> decide

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem construct (I : Instance F) (r : Row) (hr : r ∈ rows)
    (hn : I.n = 8192) (hk : I.r + I.w = 512) (hs : I.s = 64)
    (hq : Nat.card F = q) (ht : I.t = r.t)
    (coeffs : List ℕ)
    (hvalid : CodingTheory.HahnDelsarte.certificateValid 8192 r.a 639 coeffs = true)
    (hbound : CodingTheory.HahnDelsarte.certifiedBound 8192 r.a coeffs = r.L) :
    ∃ pp : ProfileCertificate I, ∃ hp : HahnSystemCertificate I,
      pp.error ≤ (1 : ℚ)/(2^r.paperBits : ℕ) ∧
      (1 : ℚ)/(2^(r.paperBits+1) : ℕ) < pp.error ∧
      hp.error ≤ (1 : ℚ)/(2^r.hahnBits : ℕ) ∧
      (1 : ℚ)/(2^(r.hahnBits+1) : ℕ) < hp.error := by
  rcases allRows r hr with
    ⟨⟨htlo, hthi⟩, ⟨halo, hahi⟩, hleast, ⟨hmin, hcount⟩,
      hpaperUpper, hpaperLower, hhahnUpper, hhahnLower⟩
  let profile : ProfileParameters I := {
    positive_degree := by omega
    large_le := by simp only [hk, hs, hn]; omega
    query_pos := by omega
    overlap_lt := by simp only [hk, hs, hn]; omega
  }
  have hmu : profile.rankError = mu := by
    simp only [ProfileParameters.rankError, ProfileParameters.coreSize]
    rw [hn, hk, hs, hq]
    rfl
  have hfield : profile.rankError + 1 / (Nat.card F : ℚ) < 1 := by
    have hnum : mu + 1 / (q : ℚ) < 1 := by native_decide
    simpa only [hmu, hq] using hnum
  have hcol : profile.columnFloor = ratio 1087 r.t := by
    simp only [ProfileParameters.columnFloor, ProfileParameters.largeSize,
      ProfileParameters.coreSize]
    rw [hk, hs, hn, ht]
    rfl
  have hover : profile.overlapRatio = eta r.t := by
    simp only [ProfileParameters.overlapRatio, ProfileParameters.overlapSize]
    rw [hk, hs, hn, ht]
    rfl
  let pp : ProfileCertificate I := {
    toProfileParameters := profile
    cutoff := r.u
    cutoff_spec := by
      simpa only [hover, hq] using hleast
    field_error_lt_one := hfield
  }
  have hpaper : pp.error = epsilon (paperTheta r.t r.u) := by
    change ProfileAnalysis.profile (Nat.card F) profile.rankError
      (max profile.columnFloor (DiscreteThreshold.candidate (Nat.card F) r.u profile.overlapRatio)) =
      epsilon (paperTheta r.t r.u)
    rw [hmu, hcol, hover, hq]
    rfl
  have hv : CodingTheory.HahnDelsarte.certificateValid I.n r.a profile.overlapSize coeffs = true := by
    simpa [ProfileParameters.overlapSize, hn, hk, hs] using hvalid
  have hcut : profile.largeSize ≤ r.a := by
    simpa [ProfileParameters.largeSize, ProfileParameters.coreSize, hk, hs] using halo
  have hcutn : r.a ≤ I.n := by omega
  have hfloorEq : profile.columnFloorAt r.a = hahnTheta r.t r.a := by
    simp only [ProfileParameters.columnFloorAt, hahnTheta, ratio]
    rw [ht, hn]
  have hfloor : profile.columnFloorAt r.a ≤ hahnTheta r.t r.a := hfloorEq.le
  have htheta : hahnTheta r.t r.a < 1 := by
    rw [← hfloorEq]
    exact profile.columnFloorAt_lt_one (by omega) hcutn
  have hexc : DirectBinomial.HahnExcessCondition I.n I.t profile.overlapSize
      (Nat.card F) r.a (CodingTheory.HahnDelsarte.certifiedBound I.n r.a coeffs)
      (hahnTheta r.t r.a) := by
    rw [hn, ht, hq]
    simp only [ProfileParameters.overlapSize, hk, hs, hbound]
    exact Or.inr (Or.inr ⟨1, by omega, hmin, by simpa [eta, ratio] using hcount⟩)
  let hp := HahnSystemCertificate.ofHahnCertificate profile r.a coeffs
    (hahnTheta r.t r.a) hcut hcutn hv hfloor htheta hexc hfield
  have hhahn : hp.error = epsilon (hahnTheta r.t r.a) := by
    change ProfileAnalysis.profile (Nat.card F) profile.rankError (hahnTheta r.t r.a) =
      epsilon (hahnTheta r.t r.a)
    rw [hmu, hq]
    rfl
  exact ⟨pp, hp, hpaper ▸ hpaperUpper, hpaper ▸ hpaperLower,
    hhahn ▸ hhahnUpper, hhahn ▸ hhahnLower⟩

omit [Fintype F] [DecidableEq F] in
theorem certifiedRows (I : Instance F) (r : Row) (hr : r ∈ rows)
    (hn : I.n = 8192) (hk : I.r + I.w = 512) (hs : I.s = 64)
    (hq : Nat.card F = q) (ht : I.t = r.t) :
    ∃ pp : ProfileCertificate I, ∃ hp : HahnSystemCertificate I,
      pp.error ≤ (1 : ℚ)/(2^r.paperBits : ℕ) ∧
      (1 : ℚ)/(2^(r.paperBits+1) : ℕ) < pp.error ∧
      hp.error ≤ (1 : ℚ)/(2^r.hahnBits : ℕ) ∧
      (1 : ℚ)/(2^(r.hahnBits+1) : ℕ) < hp.error := by
  obtain ⟨hv, hb⟩ := selectedCertificate r
  exact construct I r hr hn hk hs hq ht (certificateData r.certificate).coefficients hv hb

variable {I : Instance F}

noncomputable def terminalProof (p : HahnSystemCertificate I) :
    (Protocol.terminal I).HahnProfileProof p := .terminal p

omit [Fintype F] [DecidableEq F] in
private theorem terminalError (p : HahnSystemCertificate I) :
    1 - (((terminalProof p).localErrors.map (1 - ·)).prod) = p.error := by
  simp [terminalProof, Protocol.HahnProfileProof.localErrors]

theorem terminalFailureBound (p : HahnSystemCertificate I) (B : ℚ)
    (hb : p.error ≤ B) (masks : Bool) (σ : I.layer.Statement)
    (W : I.WireOracle masks) (messages : (Protocol.terminal I).WireStrategy) :
    ((Finset.univ.filter fun coins : (Protocol.terminal I).chain.Coins =>
      (Protocol.terminal I).wireVerify masks σ W messages coins = true ∧
      (terminalProof p).wireExtract masks σ W messages coins = none).card : ℚ) /
      Fintype.card (Protocol.terminal I).chain.Coins ≤ B := by
  exact ((terminalProof p).wire_extraction_failure masks σ W messages).trans
    (by simpa only [terminalError] using hb)

theorem terminalSoundnessBound (p : HahnSystemCertificate I) (B : ℚ)
    (hb : p.error ≤ B) (masks : Bool) (σ : I.layer.Statement)
    (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    (W : I.WireOracle masks) (messages : (Protocol.terminal I).WireStrategy) :
    ((Finset.univ.filter fun coins : (Protocol.terminal I).chain.Coins =>
      (Protocol.terminal I).wireVerify masks σ W messages coins = true).card : ℚ) /
      Fintype.card (Protocol.terminal I).chain.Coins ≤ B := by
  exact ((terminalProof p).soundness_of_extraction masks σ hfalse W messages).trans
    (by simpa only [terminalError] using hb)

/-- Every row instantiates nonrecursive witness-extraction soundness. -/
theorem certifiedTerminalFailure (I : Instance F) (r : Row) (hr : r ∈ rows)
    (hn : I.n = 8192) (hk : I.r + I.w = 512) (hs : I.s = 64)
    (hq : Nat.card F = q) (ht : I.t = r.t) :
    ∃ p : HahnSystemCertificate I,
      ∀ (masks : Bool) (σ : I.layer.Statement) (W : I.WireOracle masks)
        (messages : (Protocol.terminal I).WireStrategy),
        ((Finset.univ.filter fun coins : (Protocol.terminal I).chain.Coins =>
          (Protocol.terminal I).wireVerify masks σ W messages coins = true ∧
          (terminalProof p).wireExtract masks σ W messages coins = none).card : ℚ) /
          Fintype.card (Protocol.terminal I).chain.Coins ≤
          (1 : ℚ)/(2^r.hahnBits : ℕ) := by
  obtain ⟨_, p, _, _, hp, _⟩ := certifiedRows I r hr hn hk hs hq ht
  exact ⟨p, fun masks σ W messages => terminalFailureBound p _ hp masks σ W messages⟩

/-- False-statement soundness follows from the same extraction certificate. -/
theorem certifiedTerminalSoundness (I : Instance F) (r : Row) (hr : r ∈ rows)
    (hn : I.n = 8192) (hk : I.r + I.w = 512) (hs : I.s = 64)
    (hq : Nat.card F = q) (ht : I.t = r.t) :
    ∀ (masks : Bool) (σ : I.layer.Statement)
      (_hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
      (W : I.WireOracle masks) (messages : (Protocol.terminal I).WireStrategy),
      ((Finset.univ.filter fun coins : (Protocol.terminal I).chain.Coins =>
        (Protocol.terminal I).wireVerify masks σ W messages coins = true).card : ℚ) /
        Fintype.card (Protocol.terminal I).chain.Coins ≤
        (1 : ℚ)/(2^r.hahnBits : ℕ) := by
  obtain ⟨_, p, _, _, hp, _⟩ := certifiedRows I r hr hn hk hs hq ht
  exact fun masks σ hfalse W messages =>
    terminalSoundnessBound p _ hp masks σ hfalse W messages


end RecursivePolygero.Benchmarks.HahnRateSixteenth
