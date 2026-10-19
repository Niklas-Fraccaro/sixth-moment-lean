import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# Genuine vertical-strip bounds from the completed-zeta Mellin integral

The theta Mellin transform converges at every complex argument by its proved
strong functional-equation pair. Taking absolute values at two real
endpoints proves an imaginary-part-independent bound for the entire
completed zeta function on every closed vertical strip.
-/

namespace Sechstmoment

open Real Complex MeasureTheory Set
open scoped Topology

noncomputable section

def mellinStripMajorant (f : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ x in Ioi (0:ℝ), ‖(x:ℂ)^((a:ℂ)-1)*f x‖+‖(x:ℂ)^((b:ℂ)-1)*f x‖

theorem mellinStripMajorant_nonneg (f : ℝ → ℂ) (a b : ℝ) :
    0 ≤ mellinStripMajorant f a b :=
  integral_nonneg (fun _ => add_nonneg (norm_nonneg _) (norm_nonneg _))

theorem mellin_norm_le_strip_majorant (f : ℝ → ℂ) (a b : ℝ) {s : ℂ}
    (ha : MellinConvergent f (a:ℂ)) (hb : MellinConvergent f (b:ℂ))
    (hs : MellinConvergent f s) (hsa : a ≤ s.re) (hsb : s.re ≤ b) :
    ‖mellin f s‖ ≤ mellinStripMajorant f a b := by
  unfold mellin mellinStripMajorant
  apply (norm_integral_le_integral_norm _).trans
  apply setIntegral_mono_on hs.norm (ha.norm.add hb.norm) measurableSet_Ioi
  intro x hx
  have hx0 : 0 < x := hx
  simp only [Pi.add_apply, smul_eq_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, sub_re, Complex.one_re, Complex.ofReal_re]
  by_cases hx1 : 1 ≤ x
  · have h := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : s.re-1 ≤ b-1)
    have hm := mul_le_mul_of_nonneg_right h (norm_nonneg (f x))
    have ha0 : 0 ≤ x^(a-1)*‖f x‖ := by positivity
    nlinarith
  · have h := Real.rpow_le_rpow_of_exponent_ge hx (le_of_not_ge hx1)
      (by linarith : a-1 ≤ s.re-1)
    have hm := mul_le_mul_of_nonneg_right h (norm_nonneg (f x))
    have hb0 : 0 ≤ x^(b-1)*‖f x‖ := by positivity
    nlinarith

theorem completedRiemannZeta₀_norm_bounded_on_strip (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖completedRiemannZeta₀ s‖ ≤ C := by
  let P := HurwitzZeta.hurwitzEvenFEPair 0
  have hm (s : ℂ) : MellinConvergent P.f_modif s :=
    (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  let C := mellinStripMajorant P.f_modif (a/2) (b/2) / 2
  refine ⟨C, div_nonneg (mellinStripMajorant_nonneg _ _ _) (by norm_num), ?_⟩
  intro s hsa hsb
  have h := mellin_norm_le_strip_majorant P.f_modif (a/2) (b/2)
    (hm _) (hm _) (hm (s/2))
    (by simp only [Complex.div_ofNat_re]; linarith)
    (by simp only [Complex.div_ofNat_re]; linarith)
  change ‖mellin P.f_modif (s/2) / 2‖ ≤ C
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right h (by norm_num)

end

end Sechstmoment
