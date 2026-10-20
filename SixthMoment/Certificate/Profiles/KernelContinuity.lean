import SixthMoment.Certificate.Profiles.BalancedContinuity
import SixthMoment.Certificate.Profiles.Denominator
import SixthMoment.Certificate.Profiles.UnbalancedContinuity


namespace SixthMoment
open Set
noncomputable section
set_option maxHeartbeats 1000000

private def gramZeroExtension (x y : Finite.Feature) (z : Fin 4 → ℝ) : ℝ :=
  match x.typ, y.typ with
  | .U, .U =>
      denominatorZeroKernelExtension (featureRealPolynomial x) (featureRealPolynomial y)
        ![z 0,z 3,z 1,z 2] +
      denominatorZeroKernelExtension (featureRealPolynomial x) (featureReflectedRealPolynomial y)
        ![z 0,z 2,z 1,z 3]
  | .V, .V =>
      denominatorZeroKernelExtension (featureRealPolynomial x) (featureRealPolynomial y) z
  | _, _ => 0

private theorem gramZeroExtension_continuous (x y : Finite.Feature) :
    Continuous (gramZeroExtension x y) := by
  unfold gramZeroExtension
  cases x.typ <;> cases y.typ
  · exact ((denominatorZeroKernelExtension_continuous _ _).comp (by fun_prop)).add
      ((denominatorZeroKernelExtension_continuous _ _).comp (by fun_prop))
  · exact continuous_const
  · exact continuous_const
  · exact denominatorZeroKernelExtension_continuous _ _

private theorem gramZeroExtension_eq (x y : Finite.Feature) (z : Fin 4 → ℝ)
    (hz : ∀ i, 0 ≤ z i) : gramZeroExtension x y z = certificateGramZeroKernel x y z := by
  unfold gramZeroExtension certificateGramZeroKernel
  cases x.typ <;> cases y.typ
  · rw [denominatorZeroKernelExtension_eq _ _ _ (by
      intro i; fin_cases i <;> simpa using hz _),
      denominatorZeroKernelExtension_eq _ _ _ (by
      intro i; fin_cases i <;> simpa using hz _)]
    rfl
  · rfl
  · rfl
  · exact denominatorZeroKernelExtension_eq _ _ z hz

theorem certificateGramZeroKernel_continuousOn_nonneg (x y : Finite.Feature) :
    ContinuousOn (certificateGramZeroKernel x y) {z | ∀ i, 0 ≤ z i} := by
  apply (gramZeroExtension_continuous x y).continuousOn.congr
  intro z hz
  exact (gramZeroExtension_eq x y z hz).symm

private def gramMinusExtension (x y : Finite.Feature) (z : Fin 4 → ℝ) : ℝ :=
  match x.typ, y.typ with
  | .U, .V =>
      denominatorMinusContinuousEvaluator (featureRealPolynomial y) (featureRealPolynomial x)
        (z 1) (z 2) (z 3) (z 0) +
      denominatorMinusContinuousEvaluator (featureRealPolynomial x) (featureReflectedRealPolynomial y)
        (z 0) (z 2) (z 3) (z 1)
  | _, _ => 0

private theorem gramMinusExtension_continuous (x y : Finite.Feature) :
    Continuous (gramMinusExtension x y) := by
  unfold gramMinusExtension
  cases x.typ <;> cases y.typ
  · exact continuous_const
  · exact (denominatorMinusContinuousEvaluator_continuous_comp _ _
      (continuous_apply 1) (continuous_apply 2) (continuous_apply 3) (continuous_apply 0)).add
      (denominatorMinusContinuousEvaluator_continuous_comp _ _
      (continuous_apply 0) (continuous_apply 2) (continuous_apply 3) (continuous_apply 1))
  · exact continuous_const
  · exact continuous_const

private theorem gramMinusExtension_eq (x y : Finite.Feature) (z : Fin 4 → ℝ)
    (hz : ∀ i, 0 ≤ z i) : gramMinusExtension x y z = certificateGramMinusKernel x y z := by
  unfold gramMinusExtension certificateGramMinusKernel
  cases x.typ <;> cases y.typ
  · rfl
  · rw [← denominatorMinusKernel_eq_continuousEvaluator _ _ (hz 1) (hz 2) (hz 3) (z 0),
      ← denominatorMinusKernel_eq_continuousEvaluator _ _ (hz 0) (hz 2) (hz 3) (z 1)]
  · rfl
  · rfl

theorem certificateGramMinusKernel_continuousOn_nonneg (x y : Finite.Feature) :
    ContinuousOn (certificateGramMinusKernel x y) {z | ∀ i, 0 ≤ z i} := by
  apply (gramMinusExtension_continuous x y).continuousOn.congr
  intro z hz
  exact (gramMinusExtension_eq x y z hz).symm

end
end SixthMoment
