import SixthMoment.Arithmetic.Euler.Local.Bounds.FourTailSummability


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem coeff3_le_coeff4 (r : ℝ) (hr : 0≤r) (n : ℕ) : coeff3 r r r n≤coeff4 r r r r n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff4_succ]
    exact le_add_of_nonneg_right (mul_nonneg hr (coeff4_nonneg r hr n))
theorem coeff2_le_coeff3 (r : ℝ) (hr : 0≤r) (n : ℕ) : coeff2 r r n≤coeff3 r r r n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [coeff3_succ]
    exact le_add_of_nonneg_right (mul_nonneg hr (coeff3_nonneg r hr n))

end SixthMoment.Source.NoDPLocal
