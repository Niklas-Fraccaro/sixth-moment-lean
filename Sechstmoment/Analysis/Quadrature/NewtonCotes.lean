import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sechstmoment

open scoped BigOperators
open MeasureTheory

def ncNumerator : Fin 13 → ℤ :=
  ![1364651, 9903168, -7587864, 35725120, -51491295, 87516288,
    -87797136, 87516288, -51491295, 35725120, -7587864, 9903168, 1364651]

noncomputable def ncWeight (j : Fin 13) : ℝ := (ncNumerator j : ℝ) / 63063000

set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem nc_moments (k : Fin 13) :
    ∑ j : Fin 13, ncWeight j * ((j.val : ℝ)/12)^k.val = 1/(k.val+1) := by
  fin_cases k <;> norm_num [ncWeight, ncNumerator, Fin.sum_univ_succ]

theorem nc_polynomial_exact (c : Fin 13 → ℝ) :
    ∑ j : Fin 13, ncWeight j * (∑ k : Fin 13, c k * ((j.val : ℝ)/12)^k.val) =
      ∑ k : Fin 13, c k / (k.val+1) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    ∑ j : Fin 13, ncWeight j * (c k * ((j.val : ℝ)/12)^k.val) =
        c k * (∑ j : Fin 13, ncWeight j * ((j.val : ℝ)/12)^k.val) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = c k / (k.val+1) := by rw [nc_moments]; ring

theorem nc_integral_exact (c : Fin 13 → ℝ) :
    (∫ x in (0 : ℝ)..1, ∑ k : Fin 13, c k * x^k.val) =
      ∑ j : Fin 13, ncWeight j * (∑ k : Fin 13, c k * ((j.val : ℝ)/12)^k.val) := by
  rw [nc_polynomial_exact]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [div_eq_mul_inv]
  · intro k _
    exact (continuous_const.mul (continuous_id.pow k.val)).intervalIntegrable 0 1

end Sechstmoment
