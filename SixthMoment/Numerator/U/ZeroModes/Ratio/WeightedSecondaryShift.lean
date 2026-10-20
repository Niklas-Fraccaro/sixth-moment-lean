import SixthMoment.Numerator.U.ZeroModes.Ratio.WeightedPrimaryShift


namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioWeightedLeftResidue_line_integrable
    (L M : ℝ) {ε δ c : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hc : a03ZeroModeRatioSecondaryLine ε≤c) (hcabs : |c|≤1) (hcsep : ε≤|c|) :
    Integrable (fun y : ℝ => a03ZeroModeRatioWeightedLeftResidue L M α a b s ((c:ℂ)+(y:ℂ)*I)) :=
  a03RatioExponential_line_integrable M c _
    (a03ZeroModeRatioLeftResidueKernel_line_integrable hε hε1 hδ α hα hρ ha hb hs hc hcabs hcsep)

theorem a03ZeroModeRatioWeightedLeftResidue_horizontal_tendsto_zero
    (L M : ℝ) {ε δ l r : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hl : a03ZeroModeRatioSecondaryLine ε≤l) (hr : r≤1) (hlr : l≤r) :
    Tendsto (fun y : ℝ => ∫ c in l..r,
      a03ZeroModeRatioWeightedLeftResidue L M α a b s ((c:ℂ)+(y:ℂ)*I))
        (cocompact ℝ) (𝓝 0) := by
  apply a03RatioExponential_horizontal_tendsto_zero M l r
    (a03ZeroModeRatioLeftResidueKernel α a b s) hlr
  · intro c hc
    apply abs_le.mpr
    unfold a03ZeroModeRatioSecondaryLine at hl
    constructor <;> linarith [hc.1,hc.2]
  · exact a03ZeroModeRatioLeftResidueKernel_horizontal_majorant hε hε1 hδ α hα hρ ha hb hs hl hr hlr

theorem a03ZeroModeRatioWeightedLeftResidue_secondary_shift
    (L M : ℝ) {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re) :
    verticalIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioWeightedLeftResidue L M α a b s)=
      verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioWeightedLeftResidue L M α a b s) := by
  let U : Set ℂ := {v | 1<(a03ZeroModeRatioEulerArgument α 0 v).re ∧ v.re<0}
  have hF : DifferentiableOn ℂ (a03ZeroModeRatioWeightedLeftResidue L M α a b s) U := by
    intro v hv
    have hv0 : v≠0 := by
      intro he
      have hh := hv.2
      rw [he,zero_re] at hh
      linarith
    have hnum := a03ZeroModeRatioArithmeticNumerator_differentiableAt_comp α ha hb
      (by linarith : 1≤s.re) (U := fun _ : ℂ => 0) (V := id) (z := v)
        (by fun_prop) (by fun_prop) hv.1
    exact ((by fun_prop : DifferentiableAt ℂ (fun v : ℂ => exp ((M:ℂ)*v)) v).mul
      (hnum.div differentiableAt_id hv0)).differentiableWithinAt
  have hstrip : ∀ v : ℂ,a03ZeroModeRatioSecondaryLine ε≤v.re →
      v.re≤a03ZeroModeRatioPrimaryLine ε → v∈U := by
    intro v hl hr
    have hreg := a03ZeroModeRatio_single_residue_left_region hε (by linarith) hl
    have hA := (a03ZeroModeRatio_contour_arguments_lower hε hα hreg).2.2
    exact ⟨by linarith,by unfold a03ZeroModeRatioPrimaryLine at hr; linarith⟩
  exact SixthMoment.bblrRectangle_verticalIntegral_shift _ hF
    (by unfold a03ZeroModeRatioPrimaryLine a03ZeroModeRatioSecondaryLine; linarith) hstrip
    (a03ZeroModeRatioWeightedLeftResidue_line_integrable L M hε hε1 hδ α hα hρ ha hb hs le_rfl
      (a03ZeroModeRatioLine_abs_bounds hε hε1 2).2 (a03ZeroModeRatioLine_abs_bounds hε hε1 2).1)
    (a03ZeroModeRatioWeightedLeftResidue_line_integrable L M hε hε1 hδ α hα hρ ha hb hs
      (by unfold a03ZeroModeRatioPrimaryLine a03ZeroModeRatioSecondaryLine; linarith)
        (a03ZeroModeRatioLine_abs_bounds hε hε1 1).2 (a03ZeroModeRatioLine_abs_bounds hε hε1 1).1)
    (a03ZeroModeRatioWeightedLeftResidue_horizontal_tendsto_zero L M hε hε1 hδ α hα hρ ha hb hs le_rfl
      (by unfold a03ZeroModeRatioPrimaryLine; linarith)
        (by unfold a03ZeroModeRatioPrimaryLine a03ZeroModeRatioSecondaryLine; linarith))

theorem a03ZeroModeRatioWeightedLeftResidue_positive_shift
    (L M : ℝ) {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re) :
    verticalIntegral ε (a03ZeroModeRatioWeightedLeftResidue L M α a b s)=
      verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioWeightedLeftResidue L M α a b s)+
        a03ZeroModeRatioArithmeticNumerator α a b 0 0 s := by
  let H : ℂ→ℂ := fun v => a03ZeroModeRatioWeightedNumerator L M α a b 0 v s
  let U : Set ℂ := {v | 1<(a03ZeroModeRatioEulerArgument α 0 v).re}
  have hU : IsOpen U := by
    apply isOpen_lt continuous_const
    unfold a03ZeroModeRatioEulerArgument
    fun_prop
  have hH : DifferentiableOn ℂ H U := by
    intro v hv
    exact (a03ZeroModeRatioWeightedNumerator_differentiableAt_comp L M α ha hb
      (by linarith : 1≤s.re) (U := fun _ : ℂ => 0) (V := id) (z := v)
        (by fun_prop) (by fun_prop) hv).differentiableWithinAt
  have hstrip : ∀ v : ℂ,a03ZeroModeRatioPrimaryLine ε≤v.re → v.re≤ε → v∈U := by
    intro v hv _
    have hvs : a03ZeroModeRatioSecondaryLine ε≤v.re := by
      unfold a03ZeroModeRatioPrimaryLine at hv
      unfold a03ZeroModeRatioSecondaryLine
      linarith
    have hreg := a03ZeroModeRatio_single_residue_left_region hε (by linarith) hvs
    have hA := (a03ZeroModeRatio_contour_arguments_lower hε hα hreg).2.2
    exact lt_of_lt_of_le (by linarith : 1<1+ε) hA
  have he (v : ℂ) : H v/v=a03ZeroModeRatioWeightedLeftResidue L M α a b s v :=
    a03ZeroModeRatioWeightedNumerator_left_residue L M α a b s v
  have hleft := a03ZeroModeRatioWeightedLeftResidue_line_integrable L M hε hε1 hδ α hα hρ ha hb hs
    (c := a03ZeroModeRatioPrimaryLine ε)
    (by unfold a03ZeroModeRatioPrimaryLine a03ZeroModeRatioSecondaryLine; linarith)
      (a03ZeroModeRatioLine_abs_bounds hε hε1 1).2 (a03ZeroModeRatioLine_abs_bounds hε hε1 1).1
  have hright := a03ZeroModeRatioWeightedLeftResidue_line_integrable L M hε hε1 hδ α hα hρ ha hb hs
    (c := ε)
    (by unfold a03ZeroModeRatioSecondaryLine; linarith) (by rw [abs_of_pos hε]; linarith)
      (by rw [abs_of_pos hε])
  have hedge := a03ZeroModeRatioWeightedLeftResidue_horizontal_tendsto_zero L M hε hε1 hδ α hα hρ ha hb hs
    (l := a03ZeroModeRatioPrimaryLine ε) (r := ε)
    (by unfold a03ZeroModeRatioPrimaryLine a03ZeroModeRatioSecondaryLine; linarith)
      (by linarith) (by unfold a03ZeroModeRatioPrimaryLine; linarith)
  simp_rw [←he] at hleft hright hedge
  have hrect := SixthMoment.mellinRectangle_simplePole_shift H hU hH
    (by unfold a03ZeroModeRatioPrimaryLine; linarith) hε hstrip hleft hright hedge
  have hshift : verticalIntegral ε (a03ZeroModeRatioWeightedLeftResidue L M α a b s)=
      verticalIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioWeightedLeftResidue L M α a b s)+H 0 := by
    unfold verticalIntegral
    simp_rw [he] at hrect
    rw [hrect,mul_add]
    have hπ : (2*Real.pi:ℂ)≠0 := by exact_mod_cast (show 2*Real.pi≠0 by positivity)
    rw [←mul_assoc,one_div,inv_mul_cancel₀ hπ,one_mul]
  rw [a03ZeroModeRatioWeightedLeftResidue_secondary_shift L M hε hε1 hδ α hα hρ ha hb hs] at hshift
  simpa only [H,a03ZeroModeRatioWeightedNumerator_zero] using hshift

theorem a03ZeroModeRatioWeightedRightResidue_line_integrable
    (L M : ℝ) {ε δ c : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re)
    (hc : a03ZeroModeRatioSecondaryLine ε≤c) (hcabs : |c|≤1) (hcsep : ε≤|c|) :
    Integrable (fun y : ℝ => a03ZeroModeRatioWeightedRightResidue L M α a b s ((c:ℂ)+(y:ℂ)*I)) := by
  simpa only [a03ZeroModeRatioWeightedLeftResidue_sideSwap] using
    a03ZeroModeRatioWeightedLeftResidue_line_integrable M L hε hε1 hδ (a03ZeroModeRatioSideSwap α)
      (a03ZeroModeRatioSideSwap_small hα) (a03ZeroModeRatioSideSwap_roots_nonzero hρ) hb ha hs hc hcabs hcsep

theorem a03ZeroModeRatioWeightedRightResidue_positive_shift
    (L M : ℝ) {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1+ε≤s.re) :
    verticalIntegral ε (a03ZeroModeRatioWeightedRightResidue L M α a b s)=
      verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioWeightedRightResidue L M α a b s)+
        a03ZeroModeRatioArithmeticNumerator α a b 0 0 s := by
  have he : a03ZeroModeRatioWeightedLeftResidue M L (a03ZeroModeRatioSideSwap α) b a s=
      a03ZeroModeRatioWeightedRightResidue L M α a b s := by
    funext u
    exact a03ZeroModeRatioWeightedLeftResidue_sideSwap L M α a b s u
  simpa only [he,a03ZeroModeRatioArithmeticNumerator_sideSwap] using
    a03ZeroModeRatioWeightedLeftResidue_positive_shift M L hε hε1 hδ (a03ZeroModeRatioSideSwap α)
      (a03ZeroModeRatioSideSwap_small hα) (a03ZeroModeRatioSideSwap_roots_nonzero hρ) hb ha hs

end
end SixthMoment.Source
