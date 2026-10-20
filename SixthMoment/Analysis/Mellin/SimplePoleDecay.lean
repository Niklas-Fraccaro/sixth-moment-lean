import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import SixthMoment.Analysis.Mellin.VerticalShift


namespace SixthMoment.Source
open Complex Real Set MeasureTheory Filter
open scoped Topology
noncomputable section

theorem square_weight_norm_le_rational {z : ℂ} {t C : ℝ}
    (h : (1+|t|)^2*‖z‖ ≤ C) : ‖z‖ ≤ C/(1+t^2) := by
  apply (le_div_iff₀ (by positivity : 0 < 1+t^2)).mpr
  have hp : 1+t^2 ≤ (1+|t|)^2 := by nlinarith [sq_abs t,abs_nonneg t]
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg z)).trans (by simpa only [mul_comm] using h)

theorem simple_pole_line_integrable_of_square_decay (H : ℂ → ℂ) (hH : Continuous H)
    {a b C c : ℝ} (hc : c ∈ Icc a b) (p : ℂ) (hcp : c ≠ p.re)
    (hbound : ∀ s : ℂ, s.re ∈ Icc a b → (1+|s.im|)^2*‖H s‖ ≤ C) :
    Integrable (fun t : ℝ => H ((c:ℂ)+(t:ℂ)*I)/((c:ℂ)+(t:ℂ)*I-p)) := by
  let δ := |c-p.re|
  have hδ : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hcp)
  have hden (t : ℝ) : δ ≤ ‖(c:ℂ)+(t:ℂ)*I-p‖ := by
    simpa only [δ,sub_re,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero] using
      Complex.abs_re_le_norm ((c:ℂ)+(t:ℂ)*I-p)
  have hpath : Continuous (fun t : ℝ => (c:ℂ)+(t:ℂ)*I) := by fun_prop
  have hn (t : ℝ) : (c:ℂ)+(t:ℂ)*I-p ≠ 0 := by
    intro he
    have Hnorm := hden t
    rw [he,norm_zero] at Hnorm
    linarith
  have hcont : Continuous (fun t : ℝ => H ((c:ℂ)+(t:ℂ)*I)/((c:ℂ)+(t:ℂ)*I-p)) :=
    (hH.comp hpath).div (hpath.sub continuous_const) hn
  apply (integrable_inv_one_add_sq.const_mul (C/δ)).mono' hcont.aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  have hnum : ‖H ((c:ℂ)+(t:ℂ)*I)‖ ≤ C/(1+t^2) :=
    square_weight_norm_le_rational (by simpa using hbound ((c:ℂ)+(t:ℂ)*I) (by simpa using hc))
  rw [norm_div]
  calc
    _ ≤ ‖H ((c:ℂ)+(t:ℂ)*I)‖/δ :=
      div_le_div_of_nonneg_left (norm_nonneg _) hδ (hden t)
    _ ≤ (C/(1+t^2))/δ := div_le_div_of_nonneg_right hnum hδ.le
    _ = (C/δ)*(1+t^2)⁻¹ := by ring

theorem simple_pole_horizontal_tendsto_zero_of_square_decay (H : ℂ → ℂ)
    {a b C : ℝ} (hab : a ≤ b) (p : ℂ)
    (hbound : ∀ s : ℂ, s.re ∈ Icc a b → (1+|s.im|)^2*‖H s‖ ≤ C) :
    Tendsto (fun t : ℝ => ∫ c in a..b,
      H ((c:ℂ)+(t:ℂ)*I)/((c:ℂ)+(t:ℂ)*I-p)) (cocompact ℝ) (𝓝 0) := by
  have habs : Tendsto (fun t : ℝ => |t|) (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop
  have hv2 : Tendsto (fun t : ℝ => 1+t^2) (cocompact ℝ) atTop := by
    have h := (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp habs
    have hs : Tendsto (fun t : ℝ => t^2) (cocompact ℝ) atTop := by
      apply h.congr'
      exact Eventually.of_forall (fun t => by simp only [Function.comp_apply,sq_abs])
    exact tendsto_atTop_mono (fun t => by linarith) hs
  have hlim : Tendsto (fun t : ℝ => (C*|b-a|)*(1+t^2)⁻¹)
      (cocompact ℝ) (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using
      (tendsto_inv_atTop_zero.comp hv2).const_mul (C*|b-a|)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [habs.eventually (eventually_ge_atTop (|p.im|+1))] with t ht
  have hden (c : ℝ) : 1 ≤ ‖(c:ℂ)+(t:ℂ)*I-p‖ := by
    have habs_sub : 1 ≤ |t-p.im| := by
      have Habs := abs_add_le (t-p.im) p.im
      rw [sub_add_cancel] at Habs
      linarith
    exact habs_sub.trans (by
      simpa only [sub_im,add_im,ofReal_im,mul_I_im,ofReal_re,zero_add] using
        Complex.abs_im_le_norm ((c:ℂ)+(t:ℂ)*I-p))
  have hpoint (c : ℝ) (hc : c ∈ uIoc a b) :
      ‖H ((c:ℂ)+(t:ℂ)*I)/((c:ℂ)+(t:ℂ)*I-p)‖ ≤ C/(1+t^2) := by
    rw [uIoc_of_le hab] at hc
    have hnum : ‖H ((c:ℂ)+(t:ℂ)*I)‖ ≤ C/(1+t^2) :=
      square_weight_norm_le_rational (by
        simpa using hbound ((c:ℂ)+(t:ℂ)*I)
          (by simpa using (show c ∈ Icc a b from ⟨hc.1.le,hc.2⟩)))
    rw [norm_div]
    exact (div_le_self (norm_nonneg _) (hden c)).trans hnum
  exact (intervalIntegral.norm_integral_le_of_norm_le_const hpoint).trans_eq (by ring)

end
end SixthMoment.Source
