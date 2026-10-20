import SixthMoment.Certificate.Exact.NumeratorIntegral

namespace SixthMoment
open _root_.SixthMoment.Finite
open scoped BigOperators

def datumFeature (d : TestDatum) : Feature :=
  ⟨d.typ, d.A, d.B, (List.range 5).map fun k =>
    d.coefficient*coef (cheb d.degree) k⟩

def rawNumeratorInteger : Int :=
  Finite.sum (certificate.map fun d => numeratorFeatureInteger (datumFeature d))

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem raw_numerator_integer_exact : rawNumeratorInteger =
    930568882094372558575943745133742918423060187361605230240287840764380552571003174603513856 :=
  by decide +kernel

theorem raw_numerator_integer_aggregation : rawNumeratorInteger = numeratorInteger := by
  rw [raw_numerator_integer_exact, numerator_integer_exact]

theorem datum_feature_lengths : ∀ d ∈ certificate,
    (datumFeature d).A ≤ numeratorSecondMass (datumFeature d) := by decide +kernel

noncomputable def originalNumeratorKernel : ℝ :=
  (certificate.map fun d => numeratorFeatureKernel (datumFeature d)).sum

theorem originalNumeratorKernel_normalization :
    (rawNumeratorInteger : ℝ)/(numeratorDenominator : ℝ) = originalNumeratorKernel := by
  unfold rawNumeratorInteger originalNumeratorKernel
  rw [integer_sum_cast, List.map_map, div_eq_mul_inv, ← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  change (numeratorFeatureInteger (datumFeature d) : ℝ)*(numeratorDenominator : ℝ)⁻¹ = _
  simpa only [div_eq_mul_inv] using numeratorFeatureInteger_kernel (datum_feature_lengths d hd)

theorem originalNumeratorKernel_eq_finite : originalNumeratorKernel = (finiteNumerator : ℝ) := by
  rw [← originalNumeratorKernel_normalization, raw_numerator_integer_aggregation]
  unfold finiteNumerator
  push_cast
  rfl

theorem datum_coefficient (d : TestDatum) (r : Fin 5) :
    coef (datumFeature d).poly r.val = d.coefficient*coef (cheb d.degree) r.val := by
  simp [coef, datumFeature, r.isLt]

theorem numeratorPointKernel_smul (p : Fin 5 → ℝ) (a b c : ℝ) (hab : a ≤ b) :
    numeratorPointKernel (fun r => c*p r) a b = c*numeratorPointKernel p a b := by
  rw [numeratorPointKernel_polynomial _ hab, numeratorPointKernel_polynomial _ hab,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

theorem datumFeatureKernel_weighted {d : TestDatum} (hd : d ∈ certificate) :
    numeratorFeatureKernel (datumFeature d) = (d.coefficient : ℝ)*
      numeratorPointKernel (fun r => (coef (cheb d.degree) r.val : ℝ))
        ((d.A : ℝ)/(Finite.base : ℝ))
        ((numeratorSecondMass (datumFeature d) : ℝ)/(Finite.base : ℝ)) := by
  unfold numeratorFeatureKernel
  simp_rw [datum_coefficient, Int.cast_mul]
  change numeratorPointKernel (fun r => (d.coefficient : ℝ)*(coef (cheb d.degree) r.val : ℝ))
    ((d.A : ℝ)/(Finite.base : ℝ)) _ = _
  apply numeratorPointKernel_smul
  apply div_le_div_of_nonneg_right
  · exact_mod_cast datum_feature_lengths d hd
  · norm_num [Finite.base]

theorem original_numerator_sum_250 :
    (certificate.map fun d => (d.coefficient : ℝ)*
      numeratorPointKernel (fun r => (coef (cheb d.degree) r.val : ℝ))
        ((d.A : ℝ)/(Finite.base : ℝ))
        ((numeratorSecondMass (datumFeature d) : ℝ)/(Finite.base : ℝ))).sum =
      (finiteNumerator : ℝ) := by
  rw [← originalNumeratorKernel_eq_finite]
  unfold originalNumeratorKernel
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  exact (datumFeatureKernel_weighted hd).symm

end SixthMoment
