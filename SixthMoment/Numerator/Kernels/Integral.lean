import SixthMoment.Certificate.Kernels.Balanced.DirichletMoments
import SixthMoment.Certificate.Kernels.Balanced.Inner
import SixthMoment.Numerator.Kernels.Polynomial

namespace SixthMoment

open scoped BigOperators

theorem simplexExpectation_polynomial (p : Fin 5 → ℝ) (q₀ q₁ q₂ q₃ : ℝ) :
    simplexExpectation (fun x y z => evalDegreeFour p (simplexDot q₀ q₁ q₂ q₃ x y z)) =
      ∑ r : Fin 5, p r*simplexMonomialAverage r.val q₀ q₁ q₂ q₃ := by
  unfold evalDegreeFour
  rw [simplexExpectation_finsetSum]
  · simp_rw [simplexExpectation_const_mul, dirichlet_moment_le_four]
  · intro r
    unfold simplexDot
    fun_prop

noncomputable def numeratorPointKernel (p : Fin 5 → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..min a b, numeratorP (b-t) (a-t) *
    simplexExpectation (fun x y z => evalDegreeFour p
      (simplexDot (-1/2) (a-t-1/2) (1/2-b+t) (1/2) x y z))

theorem numeratorPointKernel_polynomial (p : Fin 5 → ℝ) {a b : ℝ} (hab : a ≤ b) :
    numeratorPointKernel p a b =
      ∑ r : Fin 5, p r*(∫ t in (0 : ℝ)..a, numeratorIntegrand r.val a b t) := by
  unfold numeratorPointKernel
  rw [min_eq_left hab]
  simp_rw [simplexExpectation_polynomial]
  have he (t : ℝ) : numeratorP (b-t) (a-t) *
      (∑ r : Fin 5, p r*simplexMonomialAverage r.val (-1/2) (a-t-1/2) (1/2-b+t) (1/2)) =
      ∑ r : Fin 5, p r*numeratorIntegrand r.val a b t := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    unfold numeratorIntegrand
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [intervalIntegral.integral_const_mul]
  · intro r _
    apply Continuous.intervalIntegrable
    unfold numeratorIntegrand numeratorP simplexMonomialAverage homogeneousFour
    fun_prop

end SixthMoment
