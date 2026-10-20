import SixthMoment.Arithmetic.Euler.Local.Bounds.ThreeNorm


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem norm_coeff4_le (a b c d : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r) (n : ℕ) :
    ‖coeff4 a b c d n‖≤coeff4 r r r r n := by
  exact (norm_step_le a r hr ha (coeff3 b c d) n).trans
    (step_mono r hr _ _ (norm_coeff3_le b c d r hr hb hc hd) n)
theorem coeff4_nonneg (r : ℝ) (hr : 0≤r) (n : ℕ) : 0≤coeff4 r r r r n :=
  step_nonneg r hr _ (coeff3_nonneg r hr) n

end SixthMoment.Source.NoDPLocal
