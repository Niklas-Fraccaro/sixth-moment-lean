import Sechstmoment.Arithmetic.Euler.Local.Bounds.OneNorm

/-! A sharp comparison majorant for twofold local coefficients. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem norm_coeff2_le (a b : ℂ) (r : ℝ) (hr : 0≤r) (ha : ‖a‖≤r) (hb : ‖b‖≤r) (n : ℕ) :
    ‖coeff2 a b n‖≤coeff2 r r n := by
  exact (norm_step_le a r hr ha (coeff1 b) n).trans
    (step_mono r hr _ _ (norm_coeff1_le b r hb) n)
theorem coeff2_nonneg (r : ℝ) (hr : 0≤r) (n : ℕ) : 0≤coeff2 r r n :=
  step_nonneg r hr _ (coeff1_nonneg r hr) n

end Sechstmoment.Source.NoDPLocal
