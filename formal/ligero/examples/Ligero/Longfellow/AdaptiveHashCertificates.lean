import examples.Ligero.Longfellow.AdaptiveCountCertificates

/-! Checked v7/v8 hash geometries and local challenge/query counts. -/

namespace Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized

set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def v7Hash1_v1_fs : Result :=
  { v7Hash1_v1 with certificate :=
      { v7Hash1_v1.certificate with e := 1456, g := 41, m := 1314 } }

theorem v7Hash1_v1_fs_parameters : v7Hash1_v1_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    (show v7Hash1_v1_fs.certificate.maskValid = true from by
      change v7Hash1_v1.certificate.maskValid = true
      exact v7Hash1_v1_parameters.2.2.2.2.1), ?_⟩
  exact v7Hash1_v1_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v7Hash1_v1_fs_counts : CountCertificate v7Hash1_v1_fs :=
  ⟨1773, 1732, 117, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Hash1_v2_fs : Result :=
  { v7Hash1_v1 with variant := .v2, certificate :=
      { v7Hash1_v1.certificate with e := 1484, g := 403, m := 156 } }

theorem v7Hash1_v2_fs_parameters : v7Hash1_v2_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    trivial, ?_⟩
  exact v7Hash1_v2_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v7Hash1_v2_fs_counts : CountCertificate v7Hash1_v2_fs :=
  ⟨1745, 921, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Hash2_v1_fs : Result :=
  { v7Hash2_v1 with certificate :=
      { v7Hash2_v1.certificate with e := 1496, g := 43, m := 1309 } }

theorem v7Hash2_v1_fs_parameters : v7Hash2_v1_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    (show v7Hash2_v1_fs.certificate.maskValid = true from by
      change v7Hash2_v1.certificate.maskValid = true
      exact v7Hash2_v1_parameters.2.2.2.2.1), ?_⟩
  exact v7Hash2_v1_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v7Hash2_v1_fs_counts : CountCertificate v7Hash2_v1_fs :=
  ⟨1821, 1778, 117, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Hash2_v2_fs : Result :=
  { v7Hash2_v1 with variant := .v2, certificate :=
      { v7Hash2_v1.certificate with e := 1525, g := 414, m := 159 } }

theorem v7Hash2_v2_fs_parameters : v7Hash2_v2_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    trivial, ?_⟩
  exact v7Hash2_v2_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v7Hash2_v2_fs_counts : CountCertificate v7Hash2_v2_fs :=
  ⟨1792, 947, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Hash2_v3_fs : Result := { v7Hash2_v2_fs with variant := .v3 }

theorem v7Hash2_v3_fs_parameters : v7Hash2_v3_fs.ParametersValid :=
  v7Hash2_v2_fs_parameters

def v7Hash2_v3_fs_counts : CountCertificate v7Hash2_v3_fs :=
  ⟨1792, 947, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Hash3_v1_fs : Result :=
  { v7Hash3_v1 with certificate :=
      { v7Hash3_v1.certificate with e := 1512, g := 42, m := 1340 } }

theorem v7Hash3_v1_fs_parameters : v7Hash3_v1_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    (show v7Hash3_v1_fs.certificate.maskValid = true from by
      change v7Hash3_v1.certificate.maskValid = true
      exact v7Hash3_v1_parameters.2.2.2.2.1), ?_⟩
  exact v7Hash3_v1_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v7Hash3_v1_fs_counts : CountCertificate v7Hash3_v1_fs :=
  ⟨1839, 1797, 117, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Hash3_v2_fs : Result :=
  { v7Hash3_v1 with variant := .v2, certificate :=
      { v7Hash3_v1.certificate with e := 1541, g := 419, m := 158 } }

theorem v7Hash3_v2_fs_parameters : v7Hash3_v2_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    trivial, ?_⟩
  exact v7Hash3_v2_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v7Hash3_v2_fs_counts : CountCertificate v7Hash3_v2_fs :=
  ⟨1810, 955, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Hash3_v3_fs : Result := { v7Hash3_v2_fs with variant := .v3 }

theorem v7Hash3_v3_fs_parameters : v7Hash3_v3_fs.ParametersValid :=
  v7Hash3_v2_fs_parameters

def v7Hash3_v3_fs_counts : CountCertificate v7Hash3_v3_fs :=
  ⟨1810, 955, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Hash4_v1_fs : Result :=
  { v7Hash4_v1 with certificate :=
      { v7Hash4_v1.certificate with e := 1550, g := 45, m := 1290 } }

theorem v7Hash4_v1_fs_parameters : v7Hash4_v1_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    (show v7Hash4_v1_fs.certificate.maskValid = true from by
      change v7Hash4_v1.certificate.maskValid = true
      exact v7Hash4_v1_parameters.2.2.2.2.1), ?_⟩
  exact v7Hash4_v1_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v7Hash4_v1_fs_counts : CountCertificate v7Hash4_v1_fs :=
  ⟨1885, 1840, 117, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Hash4_v2_fs : Result :=
  { v7Hash4_v1 with variant := .v2, certificate :=
      { v7Hash4_v1.certificate with e := 1580, g := 429, m := 159 } }

theorem v7Hash4_v2_fs_parameters : v7Hash4_v2_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    trivial, ?_⟩
  exact v7Hash4_v2_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v7Hash4_v2_fs_counts : CountCertificate v7Hash4_v2_fs :=
  ⟨1855, 979, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Hash4_v3_fs : Result := { v7Hash4_v2_fs with variant := .v3 }

theorem v7Hash4_v3_fs_parameters : v7Hash4_v3_fs.ParametersValid :=
  v7Hash4_v2_fs_parameters

def v7Hash4_v3_fs_counts : CountCertificate v7Hash4_v3_fs :=
  ⟨1855, 979, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash1_v1_fs : Result :=
  { v8Hash1_v1 with certificate :=
      { v8Hash1_v1.certificate with e := 1848, g := 49, m := 1483 } }

theorem v8Hash1_v1_fs_parameters : v8Hash1_v1_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    (show v8Hash1_v1_fs.certificate.maskValid = true from by
      change v8Hash1_v1.certificate.maskValid = true
      exact v8Hash1_v1_parameters.2.2.2.2.1), ?_⟩
  exact v8Hash1_v1_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v8Hash1_v1_fs_counts : CountCertificate v8Hash1_v1_fs :=
  ⟨2239, 2190, 117, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash1_v2_fs : Result :=
  { v8Hash1_v1 with variant := .v2, certificate :=
      { v8Hash1_v1.certificate with e := 1885, g := 511, m := 174 } }

theorem v8Hash1_v2_fs_parameters : v8Hash1_v2_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    trivial, ?_⟩
  exact v8Hash1_v2_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v8Hash1_v2_fs_counts : CountCertificate v8Hash1_v2_fs :=
  ⟨2202, 1167, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash1_v3_fs : Result := { v8Hash1_v2_fs with variant := .v3 }

theorem v8Hash1_v3_fs_parameters : v8Hash1_v3_fs.ParametersValid :=
  v8Hash1_v2_fs_parameters

def v8Hash1_v3_fs_counts : CountCertificate v8Hash1_v3_fs :=
  ⟨2202, 1167, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash2_v1_fs : Result :=
  { v8Hash2_v1 with certificate :=
      { v8Hash2_v1.certificate with e := 1845, g := 48, m := 1522 } }

theorem v8Hash2_v1_fs_parameters : v8Hash2_v1_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    (show v8Hash2_v1_fs.certificate.maskValid = true from by
      change v8Hash2_v1.certificate.maskValid = true
      exact v8Hash2_v1_parameters.2.2.2.2.1), ?_⟩
  exact v8Hash2_v1_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v8Hash2_v1_fs_counts : CountCertificate v8Hash2_v1_fs :=
  ⟨2235, 2187, 117, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash2_v2_fs : Result :=
  { v8Hash2_v1 with variant := .v2, certificate :=
      { v8Hash2_v1.certificate with e := 1882, g := 510, m := 174 } }

theorem v8Hash2_v2_fs_parameters : v8Hash2_v2_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    trivial, ?_⟩
  exact v8Hash2_v2_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v8Hash2_v2_fs_counts : CountCertificate v8Hash2_v2_fs :=
  ⟨2198, 1165, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash2_v3_fs : Result := { v8Hash2_v2_fs with variant := .v3 }

theorem v8Hash2_v3_fs_parameters : v8Hash2_v3_fs.ParametersValid :=
  v8Hash2_v2_fs_parameters

def v8Hash2_v3_fs_counts : CountCertificate v8Hash2_v3_fs :=
  ⟨2198, 1165, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash3_v1_fs : Result :=
  { v8Hash3_v1 with certificate :=
      { v8Hash3_v1.certificate with e := 1845, g := 48, m := 1522 } }

theorem v8Hash3_v1_fs_parameters : v8Hash3_v1_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    (show v8Hash3_v1_fs.certificate.maskValid = true from by
      change v8Hash3_v1.certificate.maskValid = true
      exact v8Hash3_v1_parameters.2.2.2.2.1), ?_⟩
  exact v8Hash3_v1_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v8Hash3_v1_fs_counts : CountCertificate v8Hash3_v1_fs :=
  ⟨2235, 2187, 117, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash3_v2_fs : Result :=
  { v8Hash3_v1 with variant := .v2, certificate :=
      { v8Hash3_v1.certificate with e := 1882, g := 510, m := 174 } }

theorem v8Hash3_v2_fs_parameters : v8Hash3_v2_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    trivial, ?_⟩
  exact v8Hash3_v2_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v8Hash3_v2_fs_counts : CountCertificate v8Hash3_v2_fs :=
  ⟨2198, 1165, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash3_v3_fs : Result := { v8Hash3_v2_fs with variant := .v3 }

theorem v8Hash3_v3_fs_parameters : v8Hash3_v3_fs.ParametersValid :=
  v8Hash3_v2_fs_parameters

def v8Hash3_v3_fs_counts : CountCertificate v8Hash3_v3_fs :=
  ⟨2198, 1165, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash4_v1_fs : Result :=
  { v8Hash4_v1 with certificate :=
      { v8Hash4_v1.certificate with e := 1845, g := 48, m := 1522 } }

theorem v8Hash4_v1_fs_parameters : v8Hash4_v1_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    (show v8Hash4_v1_fs.certificate.maskValid = true from by
      change v8Hash4_v1.certificate.maskValid = true
      exact v8Hash4_v1_parameters.2.2.2.2.1), ?_⟩
  exact v8Hash4_v1_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v8Hash4_v1_fs_counts : CountCertificate v8Hash4_v1_fs :=
  ⟨2235, 2187, 117, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash4_v2_fs : Result :=
  { v8Hash4_v1 with variant := .v2, certificate :=
      { v8Hash4_v1.certificate with e := 1882, g := 510, m := 174 } }

theorem v8Hash4_v2_fs_parameters : v8Hash4_v2_fs.ParametersValid := by
  unfold Result.ParametersValid
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide,
    trivial, ?_⟩
  exact v8Hash4_v2_fs.certificate.conditions_of_checked
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)

def v8Hash4_v2_fs_counts : CountCertificate v8Hash4_v2_fs :=
  ⟨2198, 1165, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v8Hash4_v3_fs : Result := { v8Hash4_v2_fs with variant := .v3 }

theorem v8Hash4_v3_fs_parameters : v8Hash4_v3_fs.ParametersValid :=
  v8Hash4_v2_fs_parameters

def v8Hash4_v3_fs_counts : CountCertificate v8Hash4_v3_fs :=
  ⟨2198, 1165, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

def v7Hash1_v3_fs : Result := { v7Hash1_v2_fs with variant := .v3 }

theorem v7Hash1_v3_fs_parameters : v7Hash1_v3_fs.ParametersValid :=
  v7Hash1_v2_fs_parameters

def v7Hash1_v3_fs_counts : CountCertificate v7Hash1_v3_fs :=
  ⟨1745, 921, 120, by native_decide, by native_decide,
    by native_decide, by native_decide⟩

end Ligero.Examples.Grid.LongfellowProfiledExtraction.Optimized
