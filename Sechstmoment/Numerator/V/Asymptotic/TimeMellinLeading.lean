import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.CauchyIntegral
import Sechstmoment.Analysis.Mellin.SmoothMellinEntire

/-! The leading time mass and a quantitative local Mellin error for the
actual compact dyadic weight. -/

namespace Sechstmoment.Source
open Complex Real Set Metric MeasureTheory
noncomputable section
set_option autoImplicit false

theorem compact_dyadic_mellin_one {w : ℝ → ℂ}
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) : mellin w 1 = ∫ x : ℝ, w x := by
  have hind : (Ioi (0:ℝ)).indicator w = w := by
    funext x
    by_cases hx : 0 < x
    · exact Set.indicator_of_mem hx w
    · have hw : w x = 0 := by
        apply Function.notMem_support.mp
        intro hm
        have H := hws (subset_tsupport w hm)
        linarith [H.1]
      simp [hw]
  simp only [mellin,sub_self,Complex.cpow_zero,one_smul]
  rw [← integral_indicator measurableSet_Ioi,hind]

theorem compact_dyadic_mellin_near_one {w : ℝ → ℂ} (hw : Continuous w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖mellin w (1+z)-(∫ x : ℝ, w x)‖ ≤ C*‖z‖ := by
  have hf := compact_dyadic_mellin_entire hw hws
  have hcont : Continuous (deriv (mellin w)) := hf.deriv.continuous
  obtain ⟨B,hB⟩ := (isCompact_closedBall (1:ℂ) 1).exists_bound_of_continuousOn hcont.continuousOn
  let C := max 1 B
  refine ⟨C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro z hz
  have H := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s (_ : s ∈ closedBall (1:ℂ) 1) => hf s)
    (fun s hs => (hB s hs).trans (le_max_right (1:ℝ) B))
    (convex_closedBall (1:ℂ) 1) (by simp : (1:ℂ) ∈ closedBall (1:ℂ) 1)
    (show 1+z ∈ closedBall (1:ℂ) 1 by
      simpa only [mem_closedBall,dist_eq_norm,add_sub_cancel_left] using hz)
  simpa only [compact_dyadic_mellin_one hws,add_sub_cancel_left] using H

theorem compact_dyadic_mellin_scaled_error {w : ℝ → ℂ} (hw : Continuous w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → ∀ z : ℂ, ‖z‖ ≤ L →
      ‖mellin w (1+z/(L:ℂ))-(∫ x : ℝ, w x)‖ ≤ C*‖z‖/L := by
  obtain ⟨C,hC,H⟩ := compact_dyadic_mellin_near_one hw hws
  refine ⟨C,hC,?_⟩
  intro L hL z hz
  have hnorm : ‖z/(L:ℂ)‖ = ‖z‖/L := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  have hsmall : ‖z/(L:ℂ)‖ ≤ 1 := by
    rw [hnorm]
    exact (div_le_one hL).mpr hz
  exact (H (z/(L:ℂ)) hsmall).trans_eq (by rw [hnorm]; ring)

end
end Sechstmoment.Source
