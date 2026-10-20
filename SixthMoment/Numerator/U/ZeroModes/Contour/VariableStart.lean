import SixthMoment.Numerator.U.ZeroModes.Contour.LargeShift

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03ZeroModeMainRemovedNumerator_start_horizontal_tendsto_zero {T δ c₀ : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ→ℂ)
    (hδ : 0<δ) (hδ1 : δ<1/4) (hc₀ : c₀∈Icc δ 1)
    (hρ : ∀ j : Fin 2,a03ZeroModeMainPoleRoot T σ j≠0)
    (hρb : ∀ j : Fin 2,‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    Tendsto (fun v : ℝ => ∫ c in δ..c₀,
      a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := a03ZeroModeMainKernel_large_strip_high_majorant σ N₁ N₂ a b hδ hδ1 hρb
  have hv : Tendsto (fun v : ℝ => |v|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlim := (gaussianPolynomialExponential_tendsto_zero 48 (2*Real.pi)).const_mul (C*|c₀-δ|)
  simp only [mul_zero] at hlim
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hv.eventually (eventually_ge_atTop (1:ℝ))] with v hvone
  have hn (c : ℝ) (hc : c∈uIoc δ c₀) :
      ‖a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)‖≤
        C*(1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2) := by
    rw [uIoc_of_le hc₀.1] at hc
    rw [a03ZeroModeMainRemovedNumerator_positive_strip_eq σ N₁ N₂ a b hδ hρ hρb
      (show δ≤((c:ℂ)+(v:ℂ)*I).re by simpa using hc.1.le)]
    have hz : 1≤‖(c:ℂ)+(v:ℂ)*I‖ := hvone.trans (by
      simpa using Complex.abs_im_le_norm ((c:ℂ)+(v:ℂ)*I))
    have hi := inv_le_one_of_one_le₀ hz
    apply (hbound c v (by rw [abs_of_pos (hδ.trans hc.1)]; exact hc.2.trans hc₀.2) hvone).trans
    calc
      _≤C*1*(1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2) := by gcongr
      _=_ := by ring
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hn).trans_eq (by ring)

theorem a03ZeroModeMainContour_start_to_small {T δ c₀ : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ→ℂ)
    (hδ : 0<δ) (hδ1 : δ<1/4) (hc₀ : c₀∈Icc δ 1)
    (hρ : ∀ j : Fin 2,a03ZeroModeMainPoleRoot T σ j≠0)
    (hρb : ∀ j : Fin 2,‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    verticalIntegral c₀ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ))=
      verticalIntegral δ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ)) := by
  let F (z : ℂ) : ℂ := a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b z/z
  have hd : DifferentiableOn ℂ F {z : ℂ | 0<z.re} := by
    intro z hz
    have hz0 : z≠0 := by intro he; simp [he] at hz
    exact ((a03ZeroModeMainRemovedNumerator_differentiable T σ N₁ N₂ a b z).div
      differentiableAt_id hz0).differentiableWithinAt
  have hs := bblrRectangle_verticalIntegral_shift F hd
    hc₀.1 (fun z hz _ => hδ.trans_le hz)
    (a03ZeroModeMainRemovedNumerator_large_line_integrable σ N₁ N₂ a b hδ hδ1
      ⟨le_rfl,by linarith⟩ hρ hρb)
    (a03ZeroModeMainRemovedNumerator_large_line_integrable σ N₁ N₂ a b hδ hδ1
      hc₀ hρ hρb)
    (a03ZeroModeMainRemovedNumerator_start_horizontal_tendsto_zero σ N₁ N₂ a b hδ hδ1 hc₀ hρ hρb)
  have he (c : ℝ) (hc : δ≤c) : verticalIntegral c F=
      verticalIntegral c (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ)) := by
    unfold verticalIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards [] with v
    exact a03ZeroModeMainRemovedNumerator_positive_strip_eq σ N₁ N₂ a b hδ hρ hρb
      (show δ≤((c:ℂ)+(v:ℂ)*I).re by simpa using hc)
  rw [he c₀ hc₀.1,he δ le_rfl] at hs
  exact hs



theorem a03ZeroModeMainContour_start_eq_initial {T δ c₀ : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ→ℂ)
    (hδ : 0<δ) (hδ1 : δ<1/4) (hc₀ : c₀∈Icc δ 1)
    (hρ : ∀ j : Fin 2,a03ZeroModeMainPoleRoot T σ j≠0)
    (hρb : ∀ j : Fin 2,‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    verticalIntegral c₀ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ))=
      verticalIntegral 1 (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ)) :=
  (a03ZeroModeMainContour_start_to_small σ N₁ N₂ a b hδ hδ1 hc₀ hρ hρb).trans
    (a03ZeroModeMainContour_initial_to_small σ N₁ N₂ a b hδ hδ1 hρ hρb).symm

end
end SixthMoment
