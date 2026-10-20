import Sechstmoment.Analysis.Complex.ContourShift
import Sechstmoment.Numerator.U.ZeroModes.Contour.MainShift
import Sechstmoment.Numerator.U.ZeroModes.PolarChamberInvariance
import Sechstmoment.Zeta.Bounds.MellinZetaNegativeStripGrowth

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem a03ZeroModeMainRootZetaProduct_large_strip_high_bound {T δ : ℝ}
    (σ : MomentShifts) (hδ : 0<δ) (hδ1 : δ<1/4)
    (hρ : ∀ j : Fin 2,‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    ∃ D : ℝ,0≤D ∧ ∀ z : ℂ,|z.re|≤1 → 1≤|z.im| →
      ‖a03ZeroModeMainRootZetaProduct T σ z‖≤D*Real.exp (2*Real.pi*|z.im|) := by
  obtain ⟨C,hC,hZ⟩ := riemannZeta_norm_le_exp_halfPlane_high_im (-4)
  refine ⟨C^2*Real.exp (2*Real.pi*(δ/4)),by positivity,?_⟩
  intro z hz hi
  have hr (j : Fin 2) : |(a03ZeroModeMainPoleRoot T σ j).re|≤δ/4 :=
    (Complex.abs_re_le_norm _).trans (hρ j)
  have hm (j : Fin 2) : |(a03ZeroModeMainPoleRoot T σ j).im|≤δ/4 :=
    (Complex.abs_im_le_norm _).trans (hρ j)
  have hre (j : Fin 2) : -4≤(a03ZeroModeMainRootArgument T σ j z).re := by
    fin_cases j <;> simp [a03ZeroModeMainRootArgument] <;>
      linarith [(abs_le.mp hz).1,(abs_le.mp hz).2,(abs_le.mp (hr 0)).1,
        (abs_le.mp (hr 0)).2,(abs_le.mp (hr 1)).1,(abs_le.mp (hr 1)).2]
  have hImLower (j : Fin 2) : 1≤|(a03ZeroModeMainRootArgument T σ j z).im| := by
    rw [a03ZeroModeMainRootArgument_im_abs]
    have hx : |z.im|≤|z.im-(a03ZeroModeMainPoleRoot T σ j).im|+
        |(a03ZeroModeMainPoleRoot T σ j).im| := by
      simpa using abs_add_le (z.im-(a03ZeroModeMainPoleRoot T σ j).im)
        (a03ZeroModeMainPoleRoot T σ j).im
    linarith [hm j]
  have hf (j : Fin 2) : ‖riemannZeta (a03ZeroModeMainRootArgument T σ j z)‖≤
      C*Real.exp (Real.pi*(|z.im|+δ/4)) := by
    have him : |(a03ZeroModeMainRootArgument T σ j z).im|≤2*(|z.im|+δ/4) := by
      rw [a03ZeroModeMainRootArgument_im_abs]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
      exact (abs_sub _ _).trans (add_le_add le_rfl (hm j))
    exact (hZ _ (hre j) (hImLower j)).trans (by gcongr; nlinarith [Real.pi_pos])
  unfold a03ZeroModeMainRootZetaProduct
  rw [Fin.prod_univ_two,norm_mul]
  calc
    _≤(C*Real.exp (Real.pi*(|z.im|+δ/4)))*(C*Real.exp (Real.pi*(|z.im|+δ/4))) :=
      mul_le_mul (hf 0) (hf 1) (norm_nonneg _) (by positivity)
    _=_ := by
      rw [show C*Real.exp (Real.pi*(|z.im|+δ/4))*(C*Real.exp (Real.pi*(|z.im|+δ/4)))=
        C^2*Real.exp (Real.pi*(|z.im|+δ/4))^2 by ring,←Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [mul_assoc,←Real.exp_add]
      congr 2
      ring

theorem a03ZeroModeMainKernel_large_strip_high_majorant {T δ : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ→ℂ)
    (hδ : 0<δ) (hδ1 : δ<1/4)
    (hρ : ∀ j : Fin 2,‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    ∃ C : ℝ,0≤C ∧ ∀ c v : ℝ,|c|≤1 → 1≤|v| →
      ‖a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
        (rawMomentShifts T σ) ((c:ℂ)+(v:ℂ)*I)‖≤
        C*‖(c:ℂ)+(v:ℂ)*I‖⁻¹*(1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2) := by
  obtain ⟨D,hD,hZ⟩ := a03ZeroModeMainRootZetaProduct_large_strip_high_bound σ hδ hδ1 hρ
  obtain ⟨A,hA,hAr⟩ := a03EtaMainArithmetic_strip_bound N₁ N₂ a b
    (rawMomentShifts T σ 0) (rawMomentShifts T σ 1)
    (rawMomentShifts T σ 2) (rawMomentShifts T σ 3) (by norm_num : (0:ℝ)<1)
  let C : ℝ := polarGaussianConstant T σ 1*D*A
  have hCG := polarGaussianConstant_nonneg T σ 1
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro c v hc hv
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hG : ‖polarPoleKiller T σ z‖≤polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2) :=
    (polarPoleKiller_vertical_norm_le T σ c v).trans (by
      gcongr
      exact polarGaussianConstant_le_of_abs_le T σ (by norm_num) hc)
  have hZ' : ‖a03ZeroModeMainRootZetaProduct T σ z‖≤D*Real.exp (2*Real.pi*|v|) := by
    simpa [z] using hZ z (by simpa [z] using hc) (by simpa [z] using hv)
  have hA' := hAr z (by simpa [z] using hc)
  unfold a03ZeroModeMainKernel a03EtaMainFunction
  rw [←a03ZeroModeMainRootZetaProduct_eq,norm_mul,norm_div,norm_mul]
  calc
    _≤(polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2))/‖z‖*
      ((D*Real.exp (2*Real.pi*|v|))*A) := by gcongr
    _=C*‖z‖⁻¹*(1+|v|)^48*(Real.exp (-v^2)*Real.exp (2*Real.pi*|v|)) := by dsimp [C]; ring
    _=_ := by rw [←Real.exp_add]; congr 1; ring

theorem a03ZeroModeMainRemovedNumerator_positive_strip_eq {T δ : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ→ℂ) (hδ : 0<δ)
    (hρ : ∀ j : Fin 2,a03ZeroModeMainPoleRoot T σ j≠0)
    (hρb : ∀ j : Fin 2,‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4)
    {z : ℂ} (hz : δ≤z.re) :
    a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b z/z=
      a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ) z := by
  apply a03ZeroModeMainRemovedNumerator_eq T σ N₁ N₂ a b hρ
  intro j he
  have hr := (Complex.re_le_norm (a03ZeroModeMainPoleRoot T σ j)).trans (hρb j)
  rw [he] at hz
  linarith

theorem a03ZeroModeMainRemovedNumerator_positive_line_continuous {T c : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ→ℂ) (hc : 0<c) :
    Continuous (fun v : ℝ => a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b
      ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)) := by
  apply ((a03ZeroModeMainRemovedNumerator_differentiable T σ N₁ N₂ a b).continuous.comp
    (by fun_prop : Continuous (fun v : ℝ => (c:ℂ)+(v:ℂ)*I))).div (by fun_prop)
  intro v he
  have hr := congrArg Complex.re he
  simp at hr
  linarith

theorem a03ZeroModeMainRemovedNumerator_large_line_integrable {T δ c : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ→ℂ)
    (hδ : 0<δ) (hδ1 : δ<1/4) (hc : c∈Icc δ 1)
    (hρ : ∀ j : Fin 2,a03ZeroModeMainPoleRoot T σ j≠0)
    (hρb : ∀ j : Fin 2,‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    Integrable (fun v : ℝ => a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b
      ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)) := by
  let F (v : ℝ) : ℂ := a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b
    ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)
  have hcont : Continuous F := a03ZeroModeMainRemovedNumerator_positive_line_continuous
    σ N₁ N₂ a b (hδ.trans_le hc.1)
  obtain ⟨C,hC,hbound⟩ := a03ZeroModeMainKernel_large_strip_high_majorant σ N₁ N₂ a b hδ hδ1 hρb
  obtain ⟨D,hDb⟩ := (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1)).exists_bound_of_continuousOn hcont.continuousOn
  let P : ℝ := max D 0
  have hP : 0≤P := le_max_right _ _
  have hi : Integrable (fun v : ℝ => (C*δ⁻¹+P*Real.exp 1)*
      ((1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2))) :=
    (gaussianPolynomialExponential_integrable 48 (2*Real.pi)).const_mul _
  apply hi.mono' hcont.aestronglyMeasurable
  apply Eventually.of_forall
  intro v
  have hgp : 0≤(1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2) := by positivity
  by_cases hv : 1≤|v|
  · have hz : δ≤‖(c:ℂ)+(v:ℂ)*I‖ := hc.1.trans (by
      simpa using Complex.re_le_norm ((c:ℂ)+(v:ℂ)*I))
    have hinv := inv_anti₀ hδ hz
    have he := a03ZeroModeMainRemovedNumerator_positive_strip_eq σ N₁ N₂ a b hδ hρ hρb
      (show δ≤((c:ℂ)+(v:ℂ)*I).re by simpa using hc.1)
    change ‖a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)‖≤_
    rw [he]
    apply (hbound c v (by rw [abs_of_pos (hδ.trans_le hc.1)]; exact hc.2) hv).trans
    calc
      _≤C*δ⁻¹*(1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2) := by gcongr
      _≤_ := by nlinarith [mul_nonneg (mul_nonneg hP (Real.exp_pos 1).le) hgp]
  · have hvabs : |v|≤1 := le_of_not_ge hv
    have hD : ‖F v‖≤P := (hDb v (abs_le.mp hvabs)).trans (le_max_left _ _)
    have hpoly : 1≤(1+|v|)^48 := one_le_pow₀ (by linarith [abs_nonneg v])
    have hv2 : v^2≤1 := by nlinarith [sq_abs v,abs_nonneg v]
    have he : 1≤Real.exp 1*Real.exp (2*Real.pi*|v|-v^2) := by
      rw [←Real.exp_add]
      exact Real.one_le_exp (by nlinarith [Real.pi_pos,abs_nonneg v])
    have he' : 1≤Real.exp 1*((1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2)) := by
      exact he.trans (mul_le_mul_of_nonneg_left
        (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hpoly
          (Real.exp_pos (2*Real.pi*|v|-v^2)).le)) (Real.exp_pos 1).le)
    have hb : P≤P*(Real.exp 1*((1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2))) := by nlinarith
    apply hD.trans
    nlinarith [mul_nonneg (mul_nonneg hC (inv_nonneg.mpr hδ.le)) hgp]

theorem a03ZeroModeMainRemovedNumerator_large_horizontal_tendsto_zero {T δ : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ→ℂ)
    (hδ : 0<δ) (hδ1 : δ<1/4)
    (hρ : ∀ j : Fin 2,a03ZeroModeMainPoleRoot T σ j≠0)
    (hρb : ∀ j : Fin 2,‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    Tendsto (fun v : ℝ => ∫ c in δ..1,
      a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := a03ZeroModeMainKernel_large_strip_high_majorant σ N₁ N₂ a b hδ hδ1 hρb
  have hv : Tendsto (fun v : ℝ => |v|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hlim := (gaussianPolynomialExponential_tendsto_zero 48 (2*Real.pi)).const_mul (C*|1-δ|)
  simp only [mul_zero] at hlim
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [hv.eventually (eventually_ge_atTop (1:ℝ))] with v hvone
  have hn (c : ℝ) (hc : c∈uIoc δ 1) :
      ‖a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)‖≤
        C*(1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2) := by
    rw [uIoc_of_le (by linarith : δ≤1)] at hc
    rw [a03ZeroModeMainRemovedNumerator_positive_strip_eq σ N₁ N₂ a b hδ hρ hρb
      (show δ≤((c:ℂ)+(v:ℂ)*I).re by simpa using hc.1.le)]
    have hz : 1≤‖(c:ℂ)+(v:ℂ)*I‖ := hvone.trans (by
      simpa using Complex.abs_im_le_norm ((c:ℂ)+(v:ℂ)*I))
    have hi := inv_le_one_of_one_le₀ hz
    apply (hbound c v (by rw [abs_of_pos (hδ.trans hc.1)]; exact hc.2) hvone).trans
    calc
      _≤C*1*(1+|v|)^48*Real.exp (2*Real.pi*|v|-v^2) := by gcongr
      _=_ := by ring
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hn).trans_eq (by ring)

theorem a03ZeroModeMainContour_initial_to_small {T δ : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ→ℂ)
    (hδ : 0<δ) (hδ1 : δ<1/4)
    (hρ : ∀ j : Fin 2,a03ZeroModeMainPoleRoot T σ j≠0)
    (hρb : ∀ j : Fin 2,‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4) :
    verticalIntegral 1 (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ))=
      verticalIntegral δ (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ)) := by
  let F (z : ℂ) : ℂ := a03ZeroModeMainRemovedNumerator T σ N₁ N₂ a b z/z
  have hd : DifferentiableOn ℂ F {z : ℂ | 0<z.re} := by
    intro z hz
    have hz0 : z≠0 := by intro he; simp [he] at hz
    exact ((a03ZeroModeMainRemovedNumerator_differentiable T σ N₁ N₂ a b z).div
      differentiableAt_id hz0).differentiableWithinAt
  have hs := bblrRectangle_verticalIntegral_shift F hd
    (show δ≤1 by linarith) (fun z hz _ => hδ.trans_le hz)
    (a03ZeroModeMainRemovedNumerator_large_line_integrable σ N₁ N₂ a b hδ hδ1
      ⟨le_rfl,by linarith⟩ hρ hρb)
    (a03ZeroModeMainRemovedNumerator_large_line_integrable σ N₁ N₂ a b hδ hδ1
      ⟨by linarith,le_rfl⟩ hρ hρb)
    (a03ZeroModeMainRemovedNumerator_large_horizontal_tendsto_zero σ N₁ N₂ a b hδ hδ1 hρ hρb)
  have he (c : ℝ) (hc : δ≤c) : verticalIntegral c F=
      verticalIntegral c (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ)) := by
    unfold verticalIntegral
    congr 1
    apply integral_congr_ae
    filter_upwards [] with v
    exact a03ZeroModeMainRemovedNumerator_positive_strip_eq σ N₁ N₂ a b hδ hρ hρb
      (show δ≤((c:ℂ)+(v:ℂ)*I).re by simpa using hc)
  rw [he 1 (by linarith),he δ le_rfl] at hs
  exact hs

theorem a03ZeroModeMainContour_initial_pair {T δ : ℝ}
    (σ : MomentShifts) (N₁ N₂ : ℕ) (a b : ℕ→ℂ)
    (hδ : 0<δ) (hδ1 : δ<1/4)
    (hα : ∀ j : Fin 4,‖rawMomentShifts T σ j‖≤δ/4)
    (hρ : ∀ j : Fin 2,a03ZeroModeMainPoleRoot T σ j≠0) :
    verticalIntegral 1 (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ))+
      verticalIntegral 1 (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
        (a03ZeroModeReverseNegative (rawMomentShifts T σ)))=
      a03EtaMainFunction N₁ N₂ a b (rawMomentShifts T σ) 0 := by
  have hρb (j : Fin 2) : ‖a03ZeroModeMainPoleRoot T σ j‖≤δ/4 :=
    purePolarRoot_norm_le_of_rawShifts hα (a03ZeroModeMainPoleIndex j)
  have hRα (j : Fin 4) : ‖rawMomentShifts T (a03ZeroModeReverseNegative σ) j‖≤δ/4 := by
    rw [a03_raw_shifts_reverseNegative]
    fin_cases j <;> simpa [a03ZeroModeReverseNegative] using hα _
  have hR₀ : a03ZeroModeMainPoleRoot T (a03ZeroModeReverseNegative σ) 0=
      -a03ZeroModeMainPoleRoot T σ 1 := by
    rw [a03ZeroModeMainPoleRoot_zero,a03ZeroModeMainPoleRoot_one,a03_raw_shifts_reverseNegative]
    norm_num [a03ZeroModeReverseNegative]
    ring
  have hR₁ : a03ZeroModeMainPoleRoot T (a03ZeroModeReverseNegative σ) 1=
      -a03ZeroModeMainPoleRoot T σ 0 := by
    rw [a03ZeroModeMainPoleRoot_one,a03ZeroModeMainPoleRoot_zero,a03_raw_shifts_reverseNegative]
    norm_num [a03ZeroModeReverseNegative]
    ring
  have hRρ (j : Fin 2) : a03ZeroModeMainPoleRoot T (a03ZeroModeReverseNegative σ) j≠0 := by
    fin_cases j
    · change a03ZeroModeMainPoleRoot T (a03ZeroModeReverseNegative σ) 0≠0
      rw [hR₀]; exact neg_ne_zero.mpr (hρ 1)
    · change a03ZeroModeMainPoleRoot T (a03ZeroModeReverseNegative σ) 1≠0
      rw [hR₁]; exact neg_ne_zero.mpr (hρ 0)
  have hRρb (j : Fin 2) : ‖a03ZeroModeMainPoleRoot T (a03ZeroModeReverseNegative σ) j‖≤δ/4 :=
    purePolarRoot_norm_le_of_rawShifts hRα (a03ZeroModeMainPoleIndex j)
  have hR := a03ZeroModeMainContour_initial_to_small (a03ZeroModeReverseNegative σ)
    N₁ N₂ a b hδ hδ1 hRρ hRρb
  have hG : polarPoleKiller T (a03ZeroModeReverseNegative σ)=polarPoleKiller T σ :=
    funext (a03PolarPoleKiller_reverseNegative T σ)
  rw [hG,a03_raw_shifts_reverseNegative] at hR
  rw [a03ZeroModeMainContour_initial_to_small σ N₁ N₂ a b hδ hδ1 hρ hρb,hR]
  exact a03ZeroModeMainContour_symmetric_pair σ N₁ N₂ a b hδ hδ1 hα hρ

theorem a03ZeroModeMainContour_initial_pair_eventually_eq_crossedArithmetic
    (K : Set MomentShifts) (hK : IsCompact K) {κ δ : ℝ}
    (hκ : 0<κ) (hδ : 0<δ) (hδ1 : δ<1/4)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ N₁ N₂ : ℕ,∀ a b : ℕ→ℂ,
      a03ZeroModeContourPrefactor (rawMomentShifts T σ)*
        (verticalIntegral 1 (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b (rawMomentShifts T σ))+
          verticalIntegral 1 (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ a b
            (a03ZeroModeReverseNegative (rawMomentShifts T σ))))=
        a03CrossedArithmeticSum N₁ N₂ a b (rawMomentShifts T σ) := by
  filter_upwards [compactNormalizedShifts_eventually_norm_small K hK (δ/4)
    (by positivity),eventually_gt_atTop (1:ℝ)] with T hsmall hT
  intro σ hσ N₁ N₂ a b
  have hρ (j : Fin 2) : a03ZeroModeMainPoleRoot T σ j≠0 := by
    change purePolarRoot T σ (a03ZeroModeMainPoleIndex j)≠0
    rw [purePolarRoot_normalized]
    exact div_ne_zero (norm_pos_iff.mp (hκ.trans_le (hroot σ hσ _)))
      (Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne')
  rw [a03ZeroModeMainContour_initial_pair σ N₁ N₂ a b hδ hδ1 (hsmall σ hσ) hρ]
  have hactual := a03ZeroModeMainContour_pair_eq_crossedArithmetic σ N₁ N₂ a b
    hδ hδ1 (hsmall σ hσ) hρ
  rw [a03ZeroModeMainContour_symmetric_pair σ N₁ N₂ a b hδ hδ1 (hsmall σ hσ) hρ] at hactual
  exact hactual

end
end Sechstmoment
