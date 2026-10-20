import Sechstmoment.Analysis.Alternants.AllZeroLimit


namespace Sechstmoment
open Filter MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 0

theorem expFirstSlope_eq_integral (q z : ℂ) :
    expFirstSlope q z = q*(∫ t in (0:ℝ)..1, Complex.exp ((z*q)*t)) := by
  by_cases hz : z = 0
  · simp [hz, expFirstSlope_zero, intervalIntegral.integral_const]
  rw [expFirstSlope_of_ne q z hz]
  by_cases hq : q = 0
  · simp [hq]
  have hi := integral_cexp_affine 0 1 (z*q) 0 (mul_ne_zero hz hq)
  simp only [Complex.ofReal_one, mul_one, add_zero, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero] at hi
  rw [hi]
  field_simp

theorem expFirstSlope_continuous_joint :
    Continuous (fun p : ℂ × ℂ => expFirstSlope p.1 p.2) := by
  simp_rw [expFirstSlope_eq_integral]
  fun_prop

theorem expNewtonMatrix_continuous_joint :
    Continuous (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) => expNewtonMatrix p.1 p.2) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i
  all_goals simp only [expNewtonMatrix, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, Fin.reduceFinMk]
  · fun_prop
  · apply (by fun_prop : Continuous (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) =>
      Complex.exp (p.2 j*p.1 0))).mul
    exact expFirstSlope_continuous_joint.comp (by fun_prop : Continuous
      (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) => (p.2 j,p.1 1-p.1 0)))
  · unfold expSecondNodeDifference simplexTriangleExpIntegral
    fun_prop
  · unfold expThirdNodeDifference
    exact (by fun_prop : Continuous (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) =>
      (p.2 j)^3/6)).mul
      (simplexExpGenerator_continuous_comp continuous_fst (by fun_prop))

noncomputable def exponentialAlternantRegularized (x q : Fin 4 → ℂ) : ℂ :=
  Complex.exp (x 0+x 1)*(expNewtonMatrix x q).det

theorem exponentialAlternantRegularized_eq_raw (x q : Fin 4 → ℂ)
    (hx : Function.Injective x) :
    exponentialAlternantRegularized x q = exponentialAlternant x q :=
  (exponentialAlternant_newton x q hx).symm

theorem exponentialAlternantRegularized_continuous_joint :
    Continuous (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) =>
      exponentialAlternantRegularized p.1 p.2) := by
  unfold exponentialAlternantRegularized
  exact (by fun_prop : Continuous (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) =>
      Complex.exp (p.1 0+p.1 1))).mul expNewtonMatrix_continuous_joint.matrix_det

end Sechstmoment
