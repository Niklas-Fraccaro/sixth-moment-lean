import Sechstmoment.Certificate.Gram.Integrability
import Sechstmoment.Certificate.Profiles.Limits
import Sechstmoment.Denominator.Gram.CertificateStatement
import Sechstmoment.Denominator.Gram.KernelTransport
import Sechstmoment.Denominator.Gram.MomentAsymptotic

/-! The complete D06 consumer for the unchanged original certificate.
Every upper-triangular entry is the actual projected zeta Gram moment;
its independently defined P02 kernel is obtained by exact coordinate transport.
The original 250-row test is summed through exactly 178 groups and 15931 pairs.
The two limits remain in their original order: height first, profile stage second. -/
namespace Sechstmoment
open Filter MeasureTheory Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

/-- The height and scalar profile consumers use exactly the same U/V family. -/
theorem d06CertificateActualProfiles_eq (n : ℕ) :
    certificateActualProfiles n = fun τ a => certificateEndpointProfile τ a n := by
  funext τ a
  cases τ <;> rfl

/-- The literal four support caps for one original feature pair. -/
def d06CertificatePairCaps (x y : Finite.Feature) : Fin 4 → ℝ :=
  ![d06CertificateProfileCap x.typ (realEndpoint x.A),
    d06CertificateProfileCap x.typ (realEndpoint x.B),
    d06CertificateProfileCap y.typ (realEndpoint y.A),
    d06CertificateProfileCap y.typ (realEndpoint y.B)]

/-- Every actual original Gram entry has the independently defined profile
kernel limit, including its exact factor one half. -/
theorem certificateFeatureProjectedGramMoment_normalized_tendsto
    {x y : Finite.Feature} (hx : x ∈ Finite.features) (hy : y ∈ Finite.features)
    (horder : x.typ = .V → y.typ = .V) {n : ℕ} (hn : 12 ≤ n)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ t, 0 ≤ Φ t) :
    Tendsto (fun T : ℝ => certificateFeatureProjectedGramMoment n T Φ x y /
      (T*(Real.log T)^9)) atTop
      (𝓝 (arithmeticFactor*(∫ t : ℝ, Φ t)*
        ((certificateProfileGramZero n x y+certificateProfileGramMinus n x y)/2))) := by
  obtain ⟨hx0,hx1,hxp⟩ := d06CertificateFeature_caps hx
  obtain ⟨hy0,hy1,hyp⟩ := d06CertificateFeature_caps hy
  obtain ⟨hxc0,hxc1⟩ := d06CertificateFeature_profiles_continuous hx hn
  obtain ⟨hyc0,hyc1⟩ := d06CertificateFeature_profiles_continuous hy hn
  obtain ⟨hxe0,hxe1⟩ := certificateFeature_endpoint_geometry hx
  obtain ⟨hye0,hye1⟩ := certificateFeature_endpoint_geometry hy
  have hn0 : 0<n := by omega
  have ha : ∀ i, 0<d06CertificatePairCaps x y i := by
    intro i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hy0
    · exact hy1
  have hρ : ∀ i, Continuous (d06CertificatePairProfiles n x y i) := by
    intro i
    fin_cases i
    · exact hxc0
    · exact hxc1
    · exact hyc0
    · exact hyc1
  have hρs : ∀ i, tsupport (d06CertificatePairProfiles n x y i) ⊆
      Icc 0 (d06CertificatePairCaps x y i) := by
    intro i
    fin_cases i
    · exact d06CertificateEndpointProfile_tsupport _ hxe0 hn0
    · exact d06CertificateEndpointProfile_tsupport _ hxe1 hn0
    · exact d06CertificateEndpointProfile_tsupport _ hye0 hn0
    · exact d06CertificateEndpointProfile_tsupport _ hye1 hn0
  have h := d06ProjectedPolynomialGramMoment_normalized_tendsto x.typ y.typ
    (d06CertificatePairCaps x y) ha hxp hyp (d06CertificatePairProfiles n x y) hρ hρs
    Φ hΦ hΦpos (featureTestPolynomial x) (featureTestPolynomial y)
    (featureTestPolynomial_natDegree x) (featureTestPolynomial_natDegree y)
  rw [d06GramKernel_certificate_pair n hn0 hx hy horder] at h
  simpa [certificateFeatureProjectedGramMoment,d06ProjectedPolynomialGramMoment,
    featureZetaTest,featureRawZetaTest,projectedZetaTest,d06CertificatePairProfiles,
    d06CertificateActualProfiles_eq,realEndpoint,base,Finite.base] using h

private theorem d06_list_sum_div (l : List ℝ) (r : ℝ) :
    (l.map fun x => x/r).sum = l.sum/r := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,add_div]

private theorem d06_pair_sum_limit_identity (n : ℕ) (K : ℝ) :
    (Finite.pairs.map fun ij => (if ij.1=ij.2 then (1:ℝ) else 2)*
      (K*((certificateProfileGramZero n (Finite.feature ij.1) (Finite.feature ij.2)+
        certificateProfileGramMinus n (Finite.feature ij.1) (Finite.feature ij.2))/2))).sum =
      K*certificateProfileDenominator n := by
  have h (l : List (ℕ × ℕ)) :
      (l.map fun ij => (if ij.1=ij.2 then (1:ℝ) else 2)*
        (K*((certificateProfileGramZero n (Finite.feature ij.1) (Finite.feature ij.2)+
          certificateProfileGramMinus n (Finite.feature ij.1) (Finite.feature ij.2))/2))).sum =
      K*((l.map fun ij => (if ij.1=ij.2 then (1:ℝ) else 2)*
        certificateProfileGramZero n (Finite.feature ij.1) (Finite.feature ij.2)).sum+
        (l.map fun ij => (if ij.1=ij.2 then (1:ℝ) else 2)*
          certificateProfileGramMinus n (Finite.feature ij.1) (Finite.feature ij.2)).sum)/2 := by
    induction l with
    | nil => simp
    | cons ij xs ih =>
      simp only [List.map_cons,List.sum_cons,ih]
      ring
  simpa only [certificateProfileDenominator,mul_div_assoc] using h Finite.pairs

/-- Literal original 250-row Gram-height asymptotic at each fixed common
stage n≥12, without an additional asymptotic or reconstruction hypothesis. -/
theorem d06ActualCertificateGramAsymptotic_closed : D06ActualCertificateGramAsymptotic := by
  intro Φ hΦ hΦpos n hn
  let K : ℝ := arithmeticFactor*(∫ t : ℝ, Φ t)
  have hl : Tendsto (fun T : ℝ => (Finite.pairs.map fun ij =>
      (if ij.1=ij.2 then (1:ℝ) else 2)*
        (certificateFeatureProjectedGramMoment n T Φ (Finite.feature ij.1) (Finite.feature ij.2)/
          (T*(Real.log T)^9))).sum) atTop
      (𝓝 ((Finite.pairs.map fun ij => (if ij.1=ij.2 then (1:ℝ) else 2)*
        (K*((certificateProfileGramZero n (Finite.feature ij.1) (Finite.feature ij.2)+
          certificateProfileGramMinus n (Finite.feature ij.1) (Finite.feature ij.2))/2))).sum)) := by
    apply tendsto_list_sum
    intro ij hij
    obtain ⟨hle,hjy⟩ := Finite.pair_indices_valid ij hij
    exact (certificateFeatureProjectedGramMoment_normalized_tendsto
      (certificateFeature_mem (hle.trans_lt hjy)) (certificateFeature_mem hjy)
        (d06CertificatePairs_type_order ij hij) hn Φ hΦ hΦpos).const_mul _
  rw [d06_pair_sum_limit_identity] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  rw [actual250ProjectedGramMoment_eq_certificate_pair_sum n (by omega) hT Φ hΦ]
  have hd := d06_list_sum_div (Finite.pairs.map fun ij =>
    (if ij.1=ij.2 then (1:ℝ) else 2)*
      certificateFeatureProjectedGramMoment n T Φ (Finite.feature ij.1) (Finite.feature ij.2))
    (T*(Real.log T)^9)
  rw [List.map_map] at hd
  simpa only [mul_div_assoc,Function.comp_def] using hd

/-- Both actual extreme phases and the full original Gram consumer are closed. -/
theorem d06PhaseGramIdentification_closed : D06PhaseGramIdentification :=
  ⟨d06ExtremeMinusVanishing_closed,d06ExtremePlusVanishing_closed,
    d06ActualCertificateGramAsymptotic_closed⟩

/-- The subsequent scalar profile limit is the unchanged independent endpoint
certificate denominator; no simultaneous height/profile limit is substituted. -/
theorem d06CertificateGramProfileLimit (Φ : ℝ → ℝ) :
    Tendsto (fun n : ℕ => arithmeticFactor*(∫ t : ℝ, Φ t)*certificateProfileDenominator n)
      atTop (𝓝 (arithmeticFactor*(∫ t : ℝ, Φ t)*certificatePointDenominator)) :=
  certificateProfileDenominator_tendsto_point.const_mul _

end
end Sechstmoment
