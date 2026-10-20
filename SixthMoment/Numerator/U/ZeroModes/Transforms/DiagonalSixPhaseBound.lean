import Mathlib.Analysis.Real.Pi.Bounds
import SixthMoment.Numerator.U.Replacement.GaussianTailUniform

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section

private theorem a03DiagonalSixPhase_norm_le {α : MomentShifts} {B : ℝ}
    (hB : 0 ≤ B) (hα : ∀ j : Fin 4, ‖α j‖ ≤ B) (m : Fin 6) :
    ‖bblrSixPhaseExponents α m‖ ≤ 4*B := by
  have h2 (i j : Fin 4) : ‖-α i-α j‖ ≤ 2*B := by
    have h := norm_sub_le (-α i) (α j)
    rw [norm_neg] at h
    linarith [hα i,hα j]
  have h3 : ‖-α 0-α 1-α 2‖ ≤ 3*B := by
    have h := norm_sub_le (-α 0-α 1) (α 2)
    linarith [h2 0 1,hα 2]
  have h4 : ‖-α 0-α 1-α 2-α 3‖ ≤ 4*B := by
    have h := norm_sub_le (-α 0-α 1-α 2) (α 3)
    linarith [hα 3]
  fin_cases m
  · change ‖(0:ℂ)‖ ≤ 4*B
    simpa only [norm_zero] using mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hB
  · simpa [bblrSixPhaseExponents] using h4
  · simpa [bblrSixPhaseExponents] using (h2 0 2).trans (by linarith : 2*B ≤ 4*B)
  · simpa [bblrSixPhaseExponents] using (h2 0 3).trans (by linarith : 2*B ≤ 4*B)
  · simpa [bblrSixPhaseExponents] using (h2 1 2).trans (by linarith : 2*B ≤ 4*B)
  · simpa [bblrSixPhaseExponents] using (h2 1 3).trans (by linarith : 2*B ≤ 4*B)

theorem a03DiagonalSixPhase_uniform_eventually_norm_bound {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      ∀ m : Fin 6, ∀ t ∈ Icc T (2*T),
        ‖(t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)‖ ≤ Real.exp (8*R) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop (2*π),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log 2))]
    with T hT hpT hlog
  intro σ hσ m t ht
  have hTp : 0 < T := zero_lt_one.trans hT
  have hL : 0 < Real.log T := Real.log_pos hT
  have hp : 0 < 2*π := by positivity
  have htp : 0 < t := hTp.trans_le ht.1
  have hx : 0 < t/(2*π) := div_pos htp hp
  have hx1 : 1 ≤ t/(2*π) := (le_div_iff₀ hp).mpr
    (by simpa only [one_mul] using hpT.trans ht.1)
  have hlogx0 : 0 ≤ Real.log (t/(2*π)) := Real.log_nonneg hx1
  have hxle : t/(2*π) ≤ 2*T := by
    apply (div_le_iff₀ hp).mpr
    have hp1 : 1 ≤ 2*π := by nlinarith [Real.pi_gt_three]
    nlinarith [ht.2]
  have hlogx : Real.log (t/(2*π)) ≤ 2*Real.log T := by
    have h := Real.log_le_log hx hxle
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hTp.ne'] at h
    linarith
  have hraw (j : Fin 4) : ‖rawMomentShifts T σ j‖ ≤ R/Real.log T := by
    rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_of_nonneg hL.le]
    exact div_le_div_of_nonneg_right (hσ j) hL.le
  have he := (Complex.re_le_norm (bblrSixPhaseExponents (rawMomentShifts T σ) m)).trans
    (a03DiagonalSixPhase_norm_le (div_nonneg hR hL.le) hraw m)
  have hcast : (t/(2*π):ℂ) = ((t/(2*π):ℝ):ℂ) := by push_cast; rfl
  rw [hcast,Complex.norm_cpow_eq_rpow_re_of_pos hx,Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ Real.log (t/(2*π))*(4*(R/Real.log T)) :=
      mul_le_mul_of_nonneg_left he hlogx0
    _ ≤ (2*Real.log T)*(4*(R/Real.log T)) :=
      mul_le_mul_of_nonneg_right hlogx (by positivity)
    _ = _ := by field_simp; ring


end
end SixthMoment
