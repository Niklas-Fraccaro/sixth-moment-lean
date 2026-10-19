import Sechstmoment.Arithmetic.Euler.Local.Bounds.TwoNorm

/-! A sharp comparison majorant for threefold local coefficients. -/

namespace Sechstmoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem norm_coeff3_le (a b c : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (n : ℕ) :
    ‖coeff3 a b c n‖≤coeff3 r r r n := by
  exact (norm_step_le a r hr ha (coeff2 b c) n).trans
    (step_mono r hr _ _ (norm_coeff2_le b c r hr hb hc) n)
theorem coeff3_nonneg (r : ℝ) (hr : 0≤r) (n : ℕ) : 0≤coeff3 r r r n :=
  step_nonneg r hr _ (coeff2_nonneg r hr) n

end Sechstmoment.Source.NoDPLocal
