import Sechstmoment.Analysis.Mellin.SimplePoleDecay

/-! Absolute vertical convergence and vanishing horizontal edges from a
square-decay estimate on a closed strip. -/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory Filter
open scoped Topology BigOperators
noncomputable section
set_option autoImplicit false

theorem vertical_integrable_of_square_strip_decay (F : ℂ → ℂ) (hF : Continuous F)
    {a b C c : ℝ} (hc : c ∈ Icc a b)
    (hbound : ∀ s : ℂ, s.re ∈ Icc a b → (1+|s.im|)^2*‖F s‖ ≤ C) :
    Integrable (fun t : ℝ => F ((c:ℂ)+(t:ℂ)*I)) := by
  have hcont : Continuous (fun t : ℝ => F ((c:ℂ)+(t:ℂ)*I)) :=
    hF.comp (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hcont.aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have H : ‖F ((c:ℂ)+(t:ℂ)*I)‖ ≤ C/(1+t^2) :=
    square_weight_norm_le_rational (by
      simpa using hbound ((c:ℂ)+(t:ℂ)*I) (by simpa using hc))
  simpa only [div_eq_mul_inv] using H

theorem horizontal_tendsto_zero_of_square_strip_decay (F : ℂ → ℂ)
    {a b C : ℝ} (hab : a ≤ b)
    (hbound : ∀ s : ℂ, s.re ∈ Icc a b → (1+|s.im|)^2*‖F s‖ ≤ C) :
    Tendsto (fun t : ℝ => ∫ c in a..b, F ((c:ℂ)+(t:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  have habs : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hv2 : Tendsto (fun t : ℝ => 1+t^2) (cocompact ℝ) atTop := by
    have H := (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp habs
    have hs : Tendsto (fun t : ℝ => t^2) (cocompact ℝ) atTop := by
      apply H.congr'
      exact Eventually.of_forall (fun t => by simp only [Function.comp_apply,sq_abs])
    exact tendsto_atTop_mono (fun t => by linarith) hs
  have hlim : Tendsto (fun t : ℝ => (C*|b-a|)*(1+t^2)⁻¹)
      (cocompact ℝ) (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using
      (tendsto_inv_atTop_zero.comp hv2).const_mul (C*|b-a|)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  apply Eventually.of_forall
  intro t
  have hpoint (c : ℝ) (hc : c ∈ uIoc a b) :
      ‖F ((c:ℂ)+(t:ℂ)*I)‖ ≤ C/(1+t^2) := by
    rw [uIoc_of_le hab] at hc
    apply square_weight_norm_le_rational
    simpa using hbound ((c:ℂ)+(t:ℂ)*I)
      (by simpa using (show c ∈ Icc a b from ⟨hc.1.le,hc.2⟩))
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hpoint).trans_eq (by ring)

theorem finite_poles_line_integrable_of_square_decay
    {ι : Type*} [Fintype ι] (H : ℂ → ℂ) (hH : Continuous H)
    {a b C c : ℝ} (hc : c ∈ Icc a b) (p : ι → ℂ) (hcp : ∀ i, c ≠ (p i).re)
    (hbound : ∀ s : ℂ, s.re ∈ Icc a b → (1+|s.im|)^2*‖H s‖ ≤ C) :
    Integrable (fun t : ℝ => H ((c:ℂ)+(t:ℂ)*I)/
      (∏ i : ι, ((c:ℂ)+(t:ℂ)*I-p i))) := by
  let δ : ℝ := ∏ i : ι, |c-(p i).re|
  have hδ : 0 < δ := Finset.prod_pos (fun i _ => abs_pos.mpr (sub_ne_zero.mpr (hcp i)))
  have hden (t : ℝ) : δ ≤ ‖∏ i : ι, ((c:ℂ)+(t:ℂ)*I-p i)‖ := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
    intro i _
    simpa only [sub_re,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using
      Complex.abs_re_le_norm ((c:ℂ)+(t:ℂ)*I-p i)
  have hpath : Continuous (fun t : ℝ => (c:ℂ)+(t:ℂ)*I) := by fun_prop
  have hn (t : ℝ) : (∏ i : ι, ((c:ℂ)+(t:ℂ)*I-p i)) ≠ 0 :=
    norm_pos_iff.mp (hδ.trans_le (hden t))
  have hcont : Continuous (fun t : ℝ => H ((c:ℂ)+(t:ℂ)*I)/
      (∏ i : ι, ((c:ℂ)+(t:ℂ)*I-p i))) :=
    (hH.comp hpath).div (by fun_prop) hn
  apply (integrable_inv_one_add_sq.const_mul (C/δ)).mono' hcont.aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have hnum : ‖H ((c:ℂ)+(t:ℂ)*I)‖ ≤ C/(1+t^2) :=
    square_weight_norm_le_rational (by
      simpa using hbound ((c:ℂ)+(t:ℂ)*I) (by simpa using hc))
  rw [norm_div]
  calc
    _ ≤ ‖H ((c:ℂ)+(t:ℂ)*I)‖/δ :=
      div_le_div_of_nonneg_left (norm_nonneg _) hδ (hden t)
    _ ≤ (C/(1+t^2))/δ := div_le_div_of_nonneg_right hnum hδ.le
    _ = (C/δ)*(1+t^2)⁻¹ := by ring

end
end Sechstmoment.Source
