import Sechstmoment.Arithmetic.Euler.Local.Geometric.StepNorm

/-! The onefold coefficient has the expected geometric majorant. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem norm_coeff1_le (a : ℂ) (r : ℝ) (ha : ‖a‖≤r) (n : ℕ) :
    ‖coeff1 a n‖≤coeff1 r n := by
  simp only [coeff1,norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ha n
theorem coeff1_nonneg (r : ℝ) (hr : 0≤r) (n : ℕ) : 0≤coeff1 r n := pow_nonneg hr n

end Sechstmoment.Source.NoDPLocal
