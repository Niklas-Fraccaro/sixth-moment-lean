import SixthMoment.Numerator.U.ZeroModes.Ratio.EtaBounds


namespace SixthMoment.Source
open Complex Real Set
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioPrimaryLine (ε : ℝ) : ℝ := -1/4+ε/2
def a03ZeroModeRatioSecondaryLine (ε : ℝ) : ℝ := -1/2+ε

def a03ZeroModeRatioLine (ε : ℝ) (j : Fin 3) : ℝ :=
  ![ε,a03ZeroModeRatioPrimaryLine ε,a03ZeroModeRatioSecondaryLine ε] j

theorem a03ZeroModeRatioLine_abs_bounds {ε : ℝ} (hε : 0<ε) (hε1 : ε<1/8)
    (j : Fin 3) : ε≤|a03ZeroModeRatioLine ε j| ∧ |a03ZeroModeRatioLine ε j|≤1 := by
  fin_cases j
  · simpa [a03ZeroModeRatioLine,abs_of_pos hε] using
      (show ε≤ε ∧ ε≤1 by constructor; rfl; linarith)
  · change ε≤|a03ZeroModeRatioPrimaryLine ε| ∧ |a03ZeroModeRatioPrimaryLine ε|≤1
    unfold a03ZeroModeRatioPrimaryLine
    rw [abs_of_neg (by linarith : -1/4+ε/2<0)]
    constructor <;> linarith
  · change ε≤|a03ZeroModeRatioSecondaryLine ε| ∧ |a03ZeroModeRatioSecondaryLine ε|≤1
    unfold a03ZeroModeRatioSecondaryLine
    rw [abs_of_neg (by linarith : -1/2+ε<0)]
    constructor <;> linarith

def A03ZeroModeRatioContourRegion (ε : ℝ) (u v : ℂ) : Prop :=
  a03ZeroModeRatioSecondaryLine ε≤u.re ∧
  a03ZeroModeRatioSecondaryLine ε≤v.re ∧
  a03ZeroModeRatioSecondaryLine ε≤u.re+v.re

theorem a03ZeroModeRatio_contour_arguments_lower {ε : ℝ} (hε : 0<ε)
    {α : MomentShifts} (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {u v : ℂ} (huv : A03ZeroModeRatioContourRegion ε u v) :
    ε≤(a03ZeroModeRatioDifferenceArgument α 0 u).re ∧
    ε≤(a03ZeroModeRatioDifferenceArgument α 1 v).re ∧
    1+ε≤(a03ZeroModeRatioEulerArgument α u v).re := by
  have hr (j : Fin 4) : |(α j).re|≤ε/8 :=
    (Complex.abs_re_le_norm _).trans (hα j)
  rcases huv with ⟨hu,hv,hs⟩
  simp only [a03ZeroModeRatioSecondaryLine] at hu hv hs
  rw [a03ZeroModeRatioDifferenceArgument_zero,a03ZeroModeRatioDifferenceArgument_one]
  simp only [a03ZeroModeRatioEulerArgument,add_re,sub_re,mul_re,
    one_re]
  norm_num
  constructor
  · linarith [(abs_le.mp (hr 0)).1,(abs_le.mp (hr 1)).2]
  constructor
  · linarith [(abs_le.mp (hr 2)).1,(abs_le.mp (hr 3)).2]
  · linarith [(abs_le.mp (hr 0)).1,(abs_le.mp (hr 1)).2,
      (abs_le.mp (hr 2)).1,(abs_le.mp (hr 3)).2]

theorem a03ZeroModeRatio_primary_rectangle_region {ε : ℝ} (_hε : 0<ε)
    (hε1 : ε<1/2) {u v : ℂ}
    (hu : a03ZeroModeRatioPrimaryLine ε≤u.re)
    (hv : a03ZeroModeRatioPrimaryLine ε≤v.re) :
    A03ZeroModeRatioContourRegion ε u v := by
  unfold A03ZeroModeRatioContourRegion a03ZeroModeRatioSecondaryLine
  simp only [a03ZeroModeRatioPrimaryLine] at hu hv
  exact ⟨by linarith,by linarith,by linarith⟩

theorem a03ZeroModeRatio_single_residue_left_region {ε : ℝ} (_hε : 0<ε)
    (hε1 : ε<1/2) {v : ℂ} (hv : a03ZeroModeRatioSecondaryLine ε≤v.re) :
    A03ZeroModeRatioContourRegion ε 0 v := by
  exact ⟨by simp [a03ZeroModeRatioSecondaryLine]; linarith,hv,by simpa using hv⟩

theorem a03ZeroModeRatio_single_residue_right_region {ε : ℝ} (_hε : 0<ε)
    (hε1 : ε<1/2) {u : ℂ} (hu : a03ZeroModeRatioSecondaryLine ε≤u.re) :
    A03ZeroModeRatioContourRegion ε u 0 := by
  exact ⟨hu,by simp [a03ZeroModeRatioSecondaryLine]; linarith,by simpa using hu⟩

theorem a03ZeroModeRatio_three_residual_line_sum (ε y z : ℝ) :
    (((a03ZeroModeRatioPrimaryLine ε:ℂ)+(y:ℂ)*I).re+
      ((a03ZeroModeRatioPrimaryLine ε:ℂ)+(z:ℂ)*I).re=
        a03ZeroModeRatioSecondaryLine ε) ∧
    ((0:ℂ).re+((a03ZeroModeRatioSecondaryLine ε:ℂ)+(z:ℂ)*I).re=
      a03ZeroModeRatioSecondaryLine ε) ∧
    (((a03ZeroModeRatioSecondaryLine ε:ℂ)+(y:ℂ)*I).re+(0:ℂ).re=
      a03ZeroModeRatioSecondaryLine ε) := by
  simp [a03ZeroModeRatioPrimaryLine,a03ZeroModeRatioSecondaryLine]
  ring

theorem a03ZeroModeRatio_contour_eta_uniform {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) :
    ∃ D : ℝ,0≤D ∧ ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤ε/8) →
      ∀ a b : ℕ,a≠0 → b≠0 → ∀ u v s : ℂ,1≤s.re →
      A03ZeroModeRatioContourRegion ε u v →
      ‖a03ZeroModeRatioEtaPair α a b u v s‖≤D*(a:ℝ)^δ*(b:ℝ)^δ := by
  obtain ⟨D,hD,hb⟩ := a03ZeroModeRatioEtaPair_subpower_bound hδ
  refine ⟨D,hD,?_⟩
  intro α hα a b ha hb0 u v s hs huv
  have hg := a03ZeroModeRatio_contour_arguments_lower hε hα huv
  exact hb α a b ha hb0 u v s hs (hε.le.trans hg.1) (hε.le.trans hg.2.1)
    (by linarith [hg.2.2])

end
end SixthMoment.Source
