import Sechstmoment.Certificate.Gram.Grouping
import Sechstmoment.Certificate.Profiles.GramTests
import Sechstmoment.Certificate.Profiles.Integrability
import Sechstmoment.Denominator.Gram.KernelDefinitions

namespace Sechstmoment
open Polynomial MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def d06CertificatePairProfiles (n : ℕ) (x y : Finite.Feature) : Fin 4 → ℝ → ℝ :=
  ![certificateEndpointProfile x.typ (realEndpoint x.A) n,
    certificateEndpointProfile x.typ (realEndpoint x.B) n,
    certificateEndpointProfile y.typ (realEndpoint y.A) n,
    certificateEndpointProfile y.typ (realEndpoint y.B) n]

theorem d06GramKernel_feature_coefficients (x : Finite.Feature) :
    (fun i : Fin 5 => (featureTestPolynomial x).coeff i.val) = featureRealPolynomial x := by
  funext i
  exact featureTestPolynomial_coeff x i

theorem d06GramKernel_feature_reflected_coefficients {x : Finite.Feature}
    (hx : x ∈ Finite.features) :
    (fun i : Fin 5 => (reflectedTestPolynomial (featureTestPolynomial x)).coeff i.val) =
      featureReflectedRealPolynomial x := by
  funext i
  have hp : (reflectedTestPolynomial (featureTestPolynomial x)).coeff i.val =
      (featureTestPolynomial x).coeff i.val*(-1)^i.val := by
    unfold reflectedTestPolynomial
    simpa only [C_neg,C_1,neg_one_mul] using
      (Polynomial.comp_C_mul_X_coeff (p := featureTestPolynomial x) (r := (-1 : ℝ)) (n := i.val))
  rw [hp,featureTestPolynomial_coeff]
  unfold featureReflectedRealPolynomial
  rw [d06CertificateFeatures_reflected_coefficients x hx i]
  push_cast
  rfl

private theorem d06_four_coordinates (a : Fin 4 → ℝ) : ![a 0,a 1,a 2,a 3] = a := by
  funext i
  fin_cases i <;> rfl

theorem d06ProfileKernelIntegral_eq_certificate (n : ℕ) (x y : Finite.Feature)
    (F : (Fin 4 → ℝ) → ℝ) :
    d06ProfileKernelIntegral (d06CertificatePairProfiles n x y) F =
      certificateFeatureProfileIntegral n x y F := by
  unfold d06ProfileKernelIntegral
  rw [d06ProfileIntegral_coordinates]
  unfold certificateFeatureProfileIntegral
  apply integral_congr_ae
  filter_upwards [] with z
  rw [Fin.prod_univ_four]
  rfl

theorem d06CertificateKernel_integrable (n : ℕ) (hn : 0<n)
    {x y : Finite.Feature} (hx : x ∈ Finite.features) (hy : y ∈ Finite.features)
    (F : (Fin 4 → ℝ) → ℝ) (hF : ContinuousOn F {a | ∀ i,0≤a i}) :
    Integrable (fun a : Fin 4 → ℝ =>
      (∏ i,d06CertificatePairProfiles n x y i (a i))*F a) := by
  let g : D06ProfileProductSpace → ℝ := fun z =>
    certificateEndpointProfile x.typ (realEndpoint x.A) n z.1.1 *
    certificateEndpointProfile x.typ (realEndpoint x.B) n z.1.2 *
    certificateEndpointProfile y.typ (realEndpoint y.A) n z.2.1 *
    certificateEndpointProfile y.typ (realEndpoint y.B) n z.2.2 *
      F ![z.1.1,z.1.2,z.2.1,z.2.2]
  have hg : Integrable g volume := by
    simpa only [Measure.volume_eq_prod] using
      certificateFeatureProfileIntegral_integrable n hn hx hy F hF
  apply (d06ProfileCoordinates_measurePreserving.integrable_comp_of_integrable hg).congr
  filter_upwards [] with a
  change d06CertificatePairProfiles n x y 0 (a 0)*
    d06CertificatePairProfiles n x y 1 (a 1)*
    d06CertificatePairProfiles n x y 2 (a 2)*
    d06CertificatePairProfiles n x y 3 (a 3)*F ![a 0,a 1,a 2,a 3] =
      (∏ i,d06CertificatePairProfiles n x y i (a i))*F a
  rw [Fin.prod_univ_four,d06_four_coordinates]

theorem d06CertificateKernelIntegral_add (n : ℕ) (hn : 0<n)
    {x y : Finite.Feature} (hx : x ∈ Finite.features) (hy : y ∈ Finite.features)
    (F G : (Fin 4 → ℝ) → ℝ)
    (hF : ContinuousOn F {a | ∀ i,0≤a i})
    (hG : ContinuousOn G {a | ∀ i,0≤a i}) :
    d06ProfileKernelIntegral (d06CertificatePairProfiles n x y) (fun a => F a+G a) =
      d06ProfileKernelIntegral (d06CertificatePairProfiles n x y) F +
      d06ProfileKernelIntegral (d06CertificatePairProfiles n x y) G := by
  unfold d06ProfileKernelIntegral
  simp_rw [mul_add]
  exact integral_add (d06CertificateKernel_integrable n hn hx hy F hF)
    (d06CertificateKernel_integrable n hn hx hy G hG)

theorem d06ZeroKernel_permuted_continuousOn (p q : Fin 5 → ℝ)
    (e : Fin 4 ≃ Fin 4) :
    ContinuousOn (fun a : Fin 4 → ℝ => denominatorZeroKernel p q
      (a (e 0)) (a (e 1)) (a (e 2)) (a (e 3))) {a | ∀ i,0≤a i} := by
  exact (denominatorZeroKernel_continuousOn_nonneg p q).comp
    (by fun_prop : ContinuousOn (fun a : Fin 4 → ℝ => fun i => a (e i)) {a | ∀ i,0≤a i})
    (fun a ha i => ha (e i))

theorem d06MinusKernel_permuted_continuousOn (p q : Fin 5 → ℝ)
    (e : Fin 4 ≃ Fin 4) :
    ContinuousOn (fun a : Fin 4 → ℝ => denominatorMinusKernel p q
      (a (e 0)) (a (e 1)) (a (e 2)) (a (e 3))) {a | ∀ i,0≤a i} := by
  exact (denominatorMinusKernel_continuousOn p q).comp
    (by fun_prop : ContinuousOn (fun a : Fin 4 → ℝ => fun i => a (e i)) {a | ∀ i,0≤a i})
    (fun a ha => ⟨ha (e 0),ha (e 1),ha (e 2)⟩)

theorem d06GramKernel_certificate_pair (n : ℕ) (hn : 0<n)
    {x y : Finite.Feature} (hx : x ∈ Finite.features) (hy : y ∈ Finite.features)
    (horder : x.typ = .V → y.typ = .V) :
    d06GramKernel x.typ y.typ (featureTestPolynomial x) (featureTestPolynomial y)
      (d06CertificatePairProfiles n x y) =
      (certificateProfileGramZero n x y+certificateProfileGramMinus n x y)/2 := by
  have hpx := d06GramKernel_feature_coefficients x
  have hpy := d06GramKernel_feature_coefficients y
  have hpry := d06GramKernel_feature_reflected_coefficients hy
  cases hxt : x.typ <;> cases hyt : y.typ
  · simp only [d06GramKernel,hpx,hpy,hpry,d06BalancedKernel_UUConjugate,
      d06BalancedKernel_UUReflected]
    have hadd := d06CertificateKernelIntegral_add n hn hx hy
      (fun a => denominatorZeroKernel (featureRealPolynomial x) (featureRealPolynomial y)
        (a 0) (a 3) (a 1) (a 2))
      (fun a => denominatorZeroKernel (featureRealPolynomial x) (featureReflectedRealPolynomial y)
        (a 0) (a 2) (a 1) (a 3))
      (d06ZeroKernel_permuted_continuousOn _ _ d06GramPerm0312)
      (d06ZeroKernel_permuted_continuousOn _ _ d06GramPerm0213)
    rw [← hadd,d06ProfileKernelIntegral_eq_certificate]
    simp [certificateProfileGramZero,certificateProfileGramMinus,
      certificateGramZeroKernel,certificateGramMinusKernel,hxt,hyt,
      certificateFeatureProfileIntegral]
  · simp only [d06GramKernel,hpx,hpy,hpry,d06UnbalancedPlusKernel_coordinates,
      d06UnbalancedKernel_UVReflected]
    have hadd := d06CertificateKernelIntegral_add n hn hx hy
      (fun a => denominatorMinusKernel (featureRealPolynomial y) (featureRealPolynomial x)
        (a 1) (a 2) (a 3) (a 0))
      (fun a => denominatorMinusKernel (featureRealPolynomial x) (featureReflectedRealPolynomial y)
        (a 0) (a 2) (a 3) (a 1))
      (d06MinusKernel_permuted_continuousOn _ _ d06GramPerm1230)
      (d06MinusKernel_permuted_continuousOn _ _ d06GramPerm0231)
    rw [← hadd,d06ProfileKernelIntegral_eq_certificate]
    simp [certificateProfileGramZero,certificateProfileGramMinus,
      certificateGramZeroKernel,certificateGramMinusKernel,hxt,hyt,
      certificateFeatureProfileIntegral]
  · have hh := horder hxt
    rw [hyt] at hh
    cases hh
  · simp only [d06GramKernel,hpx,hpy]
    change d06ProfileKernelIntegral (d06CertificatePairProfiles n x y)
      (fun a => denominatorZeroKernel (featureRealPolynomial x) (featureRealPolynomial y)
        (a 0) (a 1) (a 2) (a 3))/2 = _
    rw [d06ProfileKernelIntegral_eq_certificate]
    simp [certificateProfileGramZero,certificateProfileGramMinus,
      certificateGramZeroKernel,certificateGramMinusKernel,hxt,hyt,
      certificateFeatureProfileIntegral]

theorem d06GramKernel_certificate_original_pair (n : ℕ) (hn : 0<n)
    {ij : ℕ×ℕ} (hij : ij ∈ Finite.pairs) :
    d06GramKernel (Finite.feature ij.1).typ (Finite.feature ij.2).typ
      (featureTestPolynomial (Finite.feature ij.1))
      (featureTestPolynomial (Finite.feature ij.2))
      (d06CertificatePairProfiles n (Finite.feature ij.1) (Finite.feature ij.2)) =
      (certificateProfileGramZero n (Finite.feature ij.1) (Finite.feature ij.2)+
        certificateProfileGramMinus n (Finite.feature ij.1) (Finite.feature ij.2))/2 := by
  obtain ⟨hijle,hjy⟩ := Finite.pair_indices_valid ij hij
  exact d06GramKernel_certificate_pair n hn
    (certificateFeature_mem (by omega)) (certificateFeature_mem hjy)
      (d06CertificatePairs_type_order ij hij)

end
end Sechstmoment
