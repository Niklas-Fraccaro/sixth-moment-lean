import Sechstmoment.Analysis.Complex.SimplePole
import Sechstmoment.Numerator.Polar.EulerMellinKernel
import Sechstmoment.Numerator.U.Replacement.GaussianTailUniform
import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.EtaMainAnalytic
import Sechstmoment.Numerator.U.ZeroModes.Contour.ZetaBounds


namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeMainRemovedNumerator (T : ℝ) (σ : MomentShifts)
    (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (z : ℂ) : ℂ :=
  a03ZeroModeMainRemovedZeta T σ z*
    a03EtaMainArithmetic N₁ N₂ a b (rawMomentShifts T σ 0)
      (rawMomentShifts T σ 1) (rawMomentShifts T σ 2) (rawMomentShifts T σ 3) z

theorem a03ZeroModeMainRemovedNumerator_differentiable (T : ℝ) (σ : MomentShifts)
    (N₁ N₂ : ℕ) (a b : ℕ → ℂ) :
    Differentiable ℂ (a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b) :=
  (a03ZeroModeMainRemovedZeta_differentiable T σ).mul
    (a03EtaMainArithmetic_differentiable N₁ N₂ a b _ _ _ _)

theorem a03ZeroModeMainRemovedNumerator_eq (T : ℝ) (σ : MomentShifts)
    (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (hρ : ∀ j : Fin 2, a03ZeroModeMainPoleRoot T σ j≠0)
    {z : ℂ} (hz : ∀ j : Fin 2, z≠a03ZeroModeMainPoleRoot T σ j) :
    a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b z/z =
      a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ) z := by
  unfold a03ZeroModeMainRemovedNumerator a03ZeroModeMainKernel a03EtaMainFunction
  rw [a03ZeroModeMainRemovedZeta_eq T σ hρ hz]
  ring

theorem a03ZeroModeMainRemovedNumerator_zero (T : ℝ) (σ : MomentShifts)
    (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (hρ : ∀ j : Fin 2, a03ZeroModeMainPoleRoot T σ j≠0) :
    a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b 0 =
      a03EtaMainFunction N₁ N₂ a b (rawMomentShifts T σ) 0 := by
  unfold a03ZeroModeMainRemovedNumerator a03EtaMainFunction
  rw [a03ZeroModeMainRemovedZeta_eq T σ hρ (fun j => (hρ j).symm)]
  rw [polarPoleKiller_zero,one_mul]

theorem a03ZeroModeMainKernel_strip_majorant {T δ : ℝ} (σ : MomentShifts)
    (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (hδ : 0<δ) (hδ1 : δ<1/4)
    (hρb : ∀ j : Fin 2, ‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    ∃ C : ℝ, 0≤C ∧ ∀ c v : ℝ, |c|≤δ →
      (∀ j : Fin 2, δ≤‖1-a03ZeroModeMainRootArgument T σ j ((c:ℂ)+(v:ℂ)*I)‖) →
      ‖a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
        (rawMomentShifts T σ) ((c:ℂ)+(v:ℂ)*I)‖≤
        C*‖(c:ℂ)+(v:ℂ)*I‖⁻¹*(1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2) := by
  obtain ⟨D,hD,hZ⟩ := a03ZeroModeMainRootZetaProduct_strip_bound σ hδ hδ1 hρb
  obtain ⟨A,hA,hAr⟩ := a03EtaMainArithmetic_strip_bound N₁ N₂ a b
    (rawMomentShifts T σ 0) (rawMomentShifts T σ 1)
    (rawMomentShifts T σ 2) (rawMomentShifts T σ 3) hδ
  let C : ℝ := polarGaussianConstant T σ 1*D*A
  have hCG := polarGaussianConstant_nonneg T σ 1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro c v hc hsep
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hc1 : |c|≤1 := hc.trans (by linarith)
  have hG : ‖polarPoleKiller T σ z‖≤
      polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2) :=
    (polarPoleKiller_vertical_norm_le T σ c v).trans (by
      gcongr
      exact polarGaussianConstant_le_of_abs_le T σ (by norm_num) hc1)
  have hZ' : ‖a03ZeroModeMainRootZetaProduct T σ z‖≤D*Real.exp (2*Real.pi*|v|) :=
    by simpa [z] using hZ z (by simpa [z] using hc) hsep
  have hA' := hAr z (by simpa [z] using hc)
  unfold a03ZeroModeMainKernel a03EtaMainFunction
  rw [←a03ZeroModeMainRootZetaProduct_eq]
  rw [norm_mul,norm_div,norm_mul]
  calc
    _ ≤ (polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2))/‖z‖*
        ((D*Real.exp (2*Real.pi*|v|))*A) := by gcongr
    _ = C*‖z‖⁻¹*(1+|v|)^48*
        (Real.exp (-v^2)*Real.exp (2*Real.pi*|v|)) := by dsimp [C]; ring
    _ = _ := by
      rw [←Real.exp_add]
      congr 1
      ring

theorem a03ZeroModeMainRemovedNumerator_line_integrable {T δ c : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (hδ : 0<δ) (hδ1 : δ<1/4) (hc : |c|=δ)
    (hρ : ∀ j : Fin 2, a03ZeroModeMainPoleRoot T σ j≠0)
    (hρb : ∀ j : Fin 2, ‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    Integrable (fun v : ℝ => a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b
      ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)) := by
  obtain ⟨C,hC,hbound⟩ := a03ZeroModeMainKernel_strip_majorant σ N₁ N₂ a b hδ hδ1 hρb
  have hc0 : c≠0 := by intro he; simp [he] at hc; linarith
  have hcont : Continuous (fun v : ℝ => a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b
      ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)) := by
    apply ((a03ZeroModeMainRemovedNumerator_differentiable T σ N₁ N₂ a b).continuous.comp
      (by fun_prop : Continuous (fun v : ℝ => (c:ℂ)+(v:ℂ)*I))).div (by fun_prop)
    intro v hv
    have he := congrArg Complex.re hv
    simp at he
    exact hc0 he
  apply ((gaussianPolynomialExponential_integrable 48 (2*Real.pi)).const_mul
    (C*δ⁻¹)).mono' hcont.aestronglyMeasurable
  apply Eventually.of_forall
  intro v
  have hsep := a03ZeroModeMainRootArgument_line_separation σ hδ hρb hc v
  have hz (j : Fin 2) : (c:ℂ)+(v:ℂ)*I≠a03ZeroModeMainPoleRoot T σ j := by
    intro he
    have hs := hsep j
    rw [a03ZeroModeMainRootArgument_norm_distance,he,sub_self,norm_zero] at hs
    linarith
  rw [a03ZeroModeMainRemovedNumerator_eq T σ N₁ N₂ a b hρ hz]
  have hi : ‖(c:ℂ)+(v:ℂ)*I‖⁻¹≤δ⁻¹ :=
    inv_anti₀ hδ (by simpa [hc] using Complex.abs_re_le_norm ((c:ℂ)+(v:ℂ)*I))
  apply (hbound c v hc.le hsep).trans
  calc
    _ ≤ C*δ⁻¹*(1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2) := by gcongr
    _ = _ := by ring

theorem a03ZeroModeMainRemovedNumerator_horizontal_tendsto_zero {T δ : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (hδ : 0<δ) (hδ1 : δ<1/4)
    (hρ : ∀ j : Fin 2, a03ZeroModeMainPoleRoot T σ j≠0)
    (hρb : ∀ j : Fin 2, ‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    Tendsto (fun v : ℝ => ∫ c in (-δ)..δ,
      a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b ((c:ℂ)+(v:ℂ)*I)/
        ((c:ℂ)+(v:ℂ)*I)) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := a03ZeroModeMainKernel_strip_majorant σ N₁ N₂ a b hδ hδ1 hρb
  have hv : Tendsto (fun v : ℝ => |v|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlim := (gaussianPolynomialExponential_tendsto_zero 48 (2*Real.pi)).const_mul
    (C*|δ-(-δ)|)
  simp only [mul_zero] at hlim
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hv.eventually (eventually_ge_atTop (1:ℝ))] with v hvone
  have hnorm (c : ℝ) (hc : c∈uIoc (-δ) δ) :
      ‖a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b ((c:ℂ)+(v:ℂ)*I)/
        ((c:ℂ)+(v:ℂ)*I)‖≤C*(1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2) := by
    rw [uIoc_of_le (by linarith : -δ≤δ)] at hc
    have hcabs : |c|≤δ := abs_le.mpr ⟨hc.1.le,hc.2⟩
    have hsep := a03ZeroModeMainRootArgument_horizontal_separation σ hδ hδ1 hρb hvone
      (c := c)
    have hz (j : Fin 2) : (c:ℂ)+(v:ℂ)*I≠a03ZeroModeMainPoleRoot T σ j := by
      intro he
      have hs := hsep j
      rw [a03ZeroModeMainRootArgument_norm_distance,he,sub_self,norm_zero] at hs
      linarith
    rw [a03ZeroModeMainRemovedNumerator_eq T σ N₁ N₂ a b hρ hz]
    have hnormz : 1≤‖(c:ℂ)+(v:ℂ)*I‖ := hvone.trans
      (by simpa using Complex.abs_im_le_norm ((c:ℂ)+(v:ℂ)*I))
    have hi : ‖(c:ℂ)+(v:ℂ)*I‖⁻¹≤1 := inv_le_one_of_one_le₀ hnormz
    apply (hbound c v hcabs hsep).trans
    calc
      _ ≤ C*1*(1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2) := by gcongr
      _ = _ := by ring
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -δ) (b := δ) hnorm
  exact hb.trans_eq (by ring)

theorem a03ZeroModeMainContour_symmetric_shift {T δ : ℝ} (σ : MomentShifts)
    (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (hδ : 0<δ) (hδ1 : δ<1/4)
    (hρ : ∀ j : Fin 2, a03ZeroModeMainPoleRoot T σ j≠0)
    (hρb : ∀ j : Fin 2, ‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    verticalIntegral δ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
      (rawMomentShifts T σ)) =
      verticalIntegral (-δ) (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
        (rawMomentShifts T σ))+
        a03EtaMainFunction N₁ N₂ a b (rawMomentShifts T σ) 0 := by
  let H := a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b
  have hrect := mellinRectangle_simplePole_shift H isOpen_univ
    (a03ZeroModeMainRemovedNumerator_differentiable T σ N₁ N₂ a b).differentiableOn
    (by linarith : -δ<0) hδ (fun _ _ _ => mem_univ _)
    (a03ZeroModeMainRemovedNumerator_line_integrable σ N₁ N₂ a b hδ hδ1
      (by simpa using abs_of_pos hδ) hρ hρb)
    (a03ZeroModeMainRemovedNumerator_line_integrable σ N₁ N₂ a b hδ hδ1
      (abs_of_pos hδ) hρ hρb)
    (a03ZeroModeMainRemovedNumerator_horizontal_tendsto_zero σ N₁ N₂ a b hδ hδ1 hρ hρb)
  have he (c : ℝ) (hc : |c|=δ) :
      (∫ v : ℝ, H ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)) =
        ∫ v : ℝ, a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
          (rawMomentShifts T σ) ((c:ℂ)+(v:ℂ)*I) := by
    apply integral_congr_ae
    filter_upwards [] with v
    apply a03ZeroModeMainRemovedNumerator_eq T σ N₁ N₂ a b hρ
    intro j he
    have hs := a03ZeroModeMainRootArgument_line_separation σ hδ hρb hc v j
    rw [a03ZeroModeMainRootArgument_norm_distance,he,sub_self,norm_zero] at hs
    linarith
  rw [he (-δ) (by simpa using abs_of_pos hδ),he δ (abs_of_pos hδ)] at hrect
  have hzero : H 0=a03EtaMainFunction N₁ N₂ a b (rawMomentShifts T σ) 0 :=
    a03ZeroModeMainRemovedNumerator_zero T σ N₁ N₂ a b hρ
  rw [hzero] at hrect
  unfold verticalIntegral
  rw [hrect,mul_add]
  have hπ : (2*Real.pi:ℂ)≠0 := by exact_mod_cast (show 2*Real.pi≠0 by positivity)
  rw [←mul_assoc,one_div,inv_mul_cancel₀ hπ,one_mul]

theorem a03ZeroModeMainContour_symmetric_pair {T δ : ℝ} (σ : MomentShifts)
    (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (hδ : 0<δ) (hδ1 : δ<1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖≤δ/4)
    (hρ : ∀ j : Fin 2, a03ZeroModeMainPoleRoot T σ j≠0) :
    verticalIntegral δ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
      (rawMomentShifts T σ))+
      verticalIntegral δ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
        (a03ZeroModeReverseNegative (rawMomentShifts T σ))) =
      a03EtaMainFunction N₁ N₂ a b (rawMomentShifts T σ) 0 := by
  have hρb (j : Fin 2) : ‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4 :=
    purePolarRoot_norm_le_of_rawShifts hα (a03ZeroModeMainPoleIndex j)
  have hsmall (j : Fin 4) : ‖rawMomentShifts T σ j‖≤1/8 :=
    (hα j).trans (by linarith)
  rw [a03ZeroModeMainContour_reverseNegative _ (polarPoleKiller_even T σ) N₁ N₂ a b
    hsmall δ,a03ZeroModeMainContour_symmetric_shift σ N₁ N₂ a b hδ hδ1 hρ hρb]
  ring

theorem a03ZeroModeMainContour_pair_eq_crossedArithmetic {T δ : ℝ} (σ : MomentShifts)
    (N₁ N₂ : ℕ) (a b : ℕ → ℂ) (hδ : 0<δ) (hδ1 : δ<1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖≤δ/4)
    (hρ : ∀ j : Fin 2, a03ZeroModeMainPoleRoot T σ j≠0) :
    a03ZeroModeContourPrefactor (rawMomentShifts T σ)*
      (verticalIntegral δ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
        (rawMomentShifts T σ))+
        verticalIntegral δ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
          (a03ZeroModeReverseNegative (rawMomentShifts T σ)))) =
      a03CrossedArithmeticSum N₁ N₂ a b (rawMomentShifts T σ) := by
  rw [a03ZeroModeMainContour_symmetric_pair σ N₁ N₂ a b hδ hδ1 hα hρ]
  exact a03EtaMainFunction_zero_eq_crossedArithmetic N₁ N₂ a b
    (fun j => (hα j).trans (by linarith))

theorem a03ZeroModeMainContour_pair_eventually_eq_crossedArithmetic
    (K : Set MomentShifts) (hK : IsCompact K) {κ δ : ℝ}
    (hκ : 0<κ) (hδ : 0<δ) (hδ1 : δ<1/4)
    (hroot : ∀ σ∈K, ∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) :
    ∀ᶠ T : ℝ in atTop, ∀ σ∈K, ∀ N₁ N₂ : ℕ, ∀ a b : ℕ → ℂ,
      a03ZeroModeContourPrefactor (rawMomentShifts T σ)*
        (verticalIntegral δ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
          (rawMomentShifts T σ))+
          verticalIntegral δ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
            (a03ZeroModeReverseNegative (rawMomentShifts T σ)))) =
        a03CrossedArithmeticSum N₁ N₂ a b (rawMomentShifts T σ) := by
  filter_upwards [compactNormalizedShifts_eventually_norm_small K hK (δ/4)
    (by positivity),eventually_gt_atTop (1:ℝ)] with T hsmall hT
  intro σ hσ N₁ N₂ a b
  apply a03ZeroModeMainContour_pair_eq_crossedArithmetic σ N₁ N₂ a b hδ hδ1
    (hsmall σ hσ)
  intro j
  change purePolarRoot T σ (a03ZeroModeMainPoleIndex j)≠0
  rw [purePolarRoot_normalized]
  apply div_ne_zero
  · exact norm_pos_iff.mp (hκ.trans_le (hroot σ hσ _))
  · exact Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'

end
end Sechstmoment
