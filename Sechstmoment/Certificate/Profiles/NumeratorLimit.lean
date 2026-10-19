import Sechstmoment.Certificate.Profiles.U.NumeratorLimit
import Sechstmoment.Certificate.Profiles.V.Numerator

/-! Scalar concentration of the actual common profile family on all 250
original certificate rows. This is a profile-kernel limit, with no U zeta
moment asymptotic or full zeta-moment limit asserted. -/

namespace Sechstmoment
open MeasureTheory Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000

/-- The U and V filters partition the scalar sum while preserving every
original row and its original weight. -/
theorem certificate_type_filter_sum_partition (f : TestDatum → ℝ) :
    (uCertificateRows.map f).sum + (vCertificateRows.map f).sum =
      (certificate.map f).sum := by
  have h (l : List TestDatum) :
      ((l.filter (fun d => decide (d.typ = .U))).map f).sum +
        ((l.filter (fun d => decide (d.typ = .V))).map f).sum = (l.map f).sum := by
    induction l with
    | nil => simp
    | cons d ds ih =>
      cases ht : d.typ <;>
        simp [ht, ih, add_assoc, add_left_comm]
  exact h certificate

/-- Exactly 220 U rows and 30 V rows comprise the original 250 rows. -/
theorem certificate_profile_row_count :
    uCertificateRows.length + vCertificateRows.length = certificate.length ∧
      certificate.length = 250 := by
  simp [uCertificateRows_length, vCertificateRows_length, certificate_length]

/-- Actual scalar profile contribution of an original row. U rows use the
common normalized smooth family; V rows use the common beta family. -/
def certificateProfileNumeratorDatum (n : ℕ) (d : TestDatum) : ℝ :=
  (d.coefficient : ℝ) * match d.typ with
  | .U => ∫ x : ℝ, ∫ y : ℝ,
      uEndpointProfile uNormalizedBump uCertificateHstar ((d.A : ℝ)/(Finite.base : ℝ)) n x *
      uEndpointProfile uNormalizedBump uCertificateHstar ((d.B : ℝ)/(Finite.base : ℝ)) n y *
      numeratorPointKernel (fun r => (Finite.coef (Finite.cheb d.degree) r.val : ℝ)) x y
  | .V => ∫ x in (0 : ℝ)..eta, ∫ y in (0 : ℝ)..eta,
      betaScaledProfile eta n (betaProfileIndex eta ((d.A : ℝ)/base) n) x *
      betaScaledProfile eta n (betaProfileIndex eta ((d.B : ℝ)/base) n) y *
      numeratorPointKernel (vCertificatePolynomialCoefficients d) x (1-y)

/-- Literal sum over the original certificate, without aggregation or
replacement of its supplied coefficients. -/
def certificateProfileNumerator (n : ℕ) : ℝ :=
  (certificate.map (certificateProfileNumeratorDatum n)).sum

/-- The actual original 250-row profile sum splits into the two proved
scalar profile families at every stage. -/
theorem certificateProfileNumerator_eq_U_add_V (n : ℕ) :
    certificateProfileNumerator n = uCertificateProfileNumerator n +
      vCertificateBetaKernel n := by
  have hU : (uCertificateRows.map (certificateProfileNumeratorDatum n)).sum =
      uCertificateProfileNumerator n := by
    exact congrArg List.sum (List.map_congr_left (fun d hd => by
      have ht := ((mem_uCertificateRows d).mp hd).2
      simp only [certificateProfileNumeratorDatum, ht]))
  have hV : (vCertificateRows.map (certificateProfileNumeratorDatum n)).sum =
      vCertificateBetaKernel n := by
    exact congrArg List.sum (List.map_congr_left (fun d hd => by
      have ht := ((mem_vCertificateRows d).mp hd).2
      simp only [certificateProfileNumeratorDatum, ht]))
  unfold certificateProfileNumerator
  rw [← certificate_type_filter_sum_partition, hU, hV]

/-- The two endpoint subsums recover the original exact numerical
numerator through the original 250-row normalization theorem. -/
theorem certificatePointNumerator_eq_finite :
    uCertificatePointNumerator + vCertificateNumeratorKernel =
      (finiteNumerator : ℝ) := by
  rw [uCertificatePointNumerator_eq_original_subset,
    vCertificateNumeratorKernel_eq_original_V_feature_subsum,
    certificate_type_filter_sum_partition]
  calc
    (certificate.map (fun d => numeratorFeatureKernel (datumFeature d))).sum =
        (certificate.map (fun d => (d.coefficient : ℝ) *
          numeratorPointKernel (fun r => (Finite.coef (Finite.cheb d.degree) r.val : ℝ))
            ((d.A : ℝ)/(Finite.base : ℝ))
            ((numeratorSecondMass (datumFeature d) : ℝ)/(Finite.base : ℝ)))).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro d hd
      exact datumFeatureKernel_weighted hd
    _ = (finiteNumerator : ℝ) := original_numerator_sum_250

/-- Scalar concentration of the actual profiles on all 250 original
rows. This theorem has no external analytic-source hypothesis. -/
theorem certificateProfileNumerator_tendsto :
    Tendsto certificateProfileNumerator atTop (𝓝 (finiteNumerator : ℝ)) := by
  have h := uCertificateProfileNumerator_tendsto.add vCertificateBetaKernel_tendsto
  simpa only [← certificateProfileNumerator_eq_U_add_V,
    certificatePointNumerator_eq_finite] using h

end
end Sechstmoment
