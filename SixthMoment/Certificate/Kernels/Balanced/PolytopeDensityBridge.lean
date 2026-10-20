import Mathlib.Tactic.FunProp
import SixthMoment.Certificate.Kernels.Balanced.Inner
import SixthMoment.Certificate.Kernels.Balanced.RegionIntegral

namespace SixthMoment
open MeasureTheory

theorem denominator_polytope_density {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ v in denominatorRegion a b c d, g (v 0+v 1+v 2+v 3)) =
      ∫ t in 0..min (a+b) (c+d), realW6 t a b c d/6*g t := by
  have he (v : Fin 4 → ℝ) :
      g (v 0+v 1+v 2+v 3) = (fun w : Fin 4 → ℝ => g (w 0))
        (denominatorCoordinateChange v) := by
    rw [denominatorCoordinateChange_apply]
    rfl
  simp_rw [he]
  rw [denominator_original_iterated_integral ha hb hc hd (fun w => g (w 0))
    (by fun_prop)]
  simp only [Matrix.cons_val_zero, intervalIntegral.integral_const, smul_eq_mul]
  simp_rw [intervalIntegral.integral_mul_const]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  have hE : (0 : ℝ) ≤ min (a+b) (c+d) := le_min (add_nonneg ha hb) (add_nonneg hc hd)
  rw [Set.uIcc_of_le hE] at ht
  rw [realW6_integral ha hb hc hd ht.1 ht.2]
  have hc (r s : ℝ) : max (s-(t-r)) 0 = max 0 (r+s-t) := by
    have he : s-(t-r) = r+s-t := by ring
    rw [he, max_comm]
  simp_rw [hc]
  ring

noncomputable def denominatorRealInner (p q : Fin 5 → ℝ) (delta h : ℝ) : ℝ :=
  ∫ x in -h..h, evalDegreeFour p (delta-x)*evalDegreeFour q (-delta-x)

theorem denominatorRealInner_continuous (p q : Fin 5 → ℝ) (delta : ℝ)
    (h : ℝ → ℝ) (hh : Continuous h) :
    Continuous (fun t => denominatorRealInner p q delta (h t)) := by
  unfold denominatorRealInner
  simp_rw [denominator_inner_integral]
  fun_prop

noncomputable def denominatorZeroKernel (p q : Fin 5 → ℝ) (a b c d : ℝ) : ℝ :=
  let delta := (a+b-c-d)/2
  let h := fun t => (1-a-b-c-d+2*t)/2
  ∫ v in denominatorRegion a b c d,
    denominatorRealInner p q delta (h (v 0+v 1+v 2+v 3))

theorem denominatorZeroKernel_one_dimensional (p q : Fin 5 → ℝ)
    {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    denominatorZeroKernel p q a b c d =
      ∫ t in 0..min (a+b) (c+d), realW6 t a b c d/6*
        denominatorRealInner p q ((a+b-c-d)/2) ((1-a-b-c-d+2*t)/2) := by
  dsimp only [denominatorZeroKernel]
  apply denominator_polytope_density ha hb hc hd
    (fun t => denominatorRealInner p q ((a+b-c-d)/2) ((1-a-b-c-d+2*t)/2))
  apply denominatorRealInner_continuous
  fun_prop

end SixthMoment
