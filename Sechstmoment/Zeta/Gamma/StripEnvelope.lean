import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Sechstmoment.Zeta.Centering.GammaRatio

/-! Actual Gamma envelopes for quantitative tails on the original AFE line.
The reflection formula supplies the exponential cancellation; the proved
Euler-product Gamma-ratio estimate supplies the remaining polynomial factor.
-/

namespace Sechstmoment.Source
open Complex Filter Set ComplexConjugate
open scoped Topology
noncomputable section

theorem gamma_half_norm_sq (y : ℝ) :
    ‖Gamma ((1/2 : ℂ)+(y : ℂ)*I)‖^2 = Real.pi/Real.cosh (Real.pi*y) := by
  let z : ℂ := (1/2 : ℂ)+(y : ℂ)*I
  have hc : 1-z = conj z := by
    apply Complex.ext <;> norm_num [z]
  have hs : Complex.sin ((Real.pi : ℂ)*z) = (Real.cosh (Real.pi*y) : ℂ) := by
    have he : (Real.pi : ℂ)*z = ((Real.pi*y : ℝ) : ℂ)*I+Real.pi/2 := by
      dsimp [z]
      push_cast
      ring
    rw [he, Complex.sin_add_pi_div_two, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  have hr := Complex.Gamma_mul_Gamma_one_sub z
  rw [hc, Complex.Gamma_conj, Complex.mul_conj', hs] at hr
  exact_mod_cast hr

theorem cosh_exp_abs_bounds (x : ℝ) :
    Real.exp |x|/2 ≤ Real.cosh x ∧ Real.cosh x ≤ Real.exp |x| := by
  have hc : Real.cosh x = Real.cosh |x| := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, Real.cosh_neg]
  rw [hc, Real.cosh_eq]
  have hpos := Real.exp_pos (-|x|)
  have hle : Real.exp (-|x|) ≤ Real.exp |x| :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg x])
  constructor <;> linarith

theorem gamma_half_weighted_norm_sq_bounds (y : ℝ) :
    Real.pi ≤ (‖Gamma ((1/2 : ℂ)+(y : ℂ)*I)‖*
      Real.exp (Real.pi*|y|/2))^2 ∧
    (‖Gamma ((1/2 : ℂ)+(y : ℂ)*I)‖*
      Real.exp (Real.pi*|y|/2))^2 ≤ 2*Real.pi := by
  have he : (Real.exp (Real.pi*|y|/2))^2 = Real.exp (Real.pi*|y|) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hc := cosh_exp_abs_bounds (Real.pi*y)
  rw [abs_mul, abs_of_pos Real.pi_pos] at hc
  rw [mul_pow, gamma_half_norm_sq, he]
  have hcp := Real.cosh_pos (Real.pi*y)
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ hcp]
    exact mul_le_mul_of_nonneg_left hc.2 Real.pi_pos.le
  · rw [div_mul_eq_mul_div, div_le_iff₀ hcp]
    have h := mul_le_mul_of_nonneg_left hc.1 (by positivity : 0 ≤ 2*Real.pi)
    nlinarith

theorem gamma_half_weighted_norm_bounds (y : ℝ) :
    min 1 Real.pi ≤ ‖Gamma ((1/2 : ℂ)+(y : ℂ)*I)‖*
      Real.exp (Real.pi*|y|/2) ∧
    ‖Gamma ((1/2 : ℂ)+(y : ℂ)*I)‖*
      Real.exp (Real.pi*|y|/2) ≤ 2*Real.pi+1 := by
  let H := ‖Gamma ((1/2 : ℂ)+(y : ℂ)*I)‖*Real.exp (Real.pi*|y|/2)
  have hb := gamma_half_weighted_norm_sq_bounds y
  change Real.pi ≤ H^2 ∧ H^2 ≤ 2*Real.pi at hb
  have hp := Real.pi_pos
  have hH : 0 ≤ H := by dsimp [H]; positivity
  constructor
  · change min 1 Real.pi ≤ H
    by_cases h : 1 ≤ H
    · exact (min_le_left _ _).trans h
    · have hs : H^2 ≤ H := by nlinarith
      exact (min_le_right _ _).trans (hb.1.trans hs)
  · change H ≤ 2*Real.pi+1
    nlinarith [sq_nonneg (H-1)]

theorem gamma_strip_large_relative (σ y : ℝ) (hσ : σ ∈ Icc (1/8 : ℝ) (7/8))
    (hy : 20 ≤ |y|) :
    ‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖ ≤
      2*(1+|y|)*‖Gamma ((1/2 : ℂ)+(y : ℂ)*I)‖ ∧
    ‖Gamma ((1/2 : ℂ)+(y : ℂ)*I)‖ ≤
      2*(1+|y|)*‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖ := by
  let s : ℂ := (1/2 : ℂ)+(y : ℂ)*I
  let u : ℂ := ((σ-1/2 : ℝ) : ℂ)
  let R : ℂ := (Gamma (s+u)/Gamma s)/s^u
  have hsu : s+u = (σ : ℂ)+(y : ℂ)*I := by dsimp [s,u]; push_cast; ring
  have hus : ‖u‖ ≤ 1/2 := by
    dsimp [u]
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩
  have hsi : s.im = y := by simp [s]
  have hsr : s.re = 1/2 := by simp [s]
  have he : ‖R-1‖ ≤ 1/2 := by
    have hr := Sechstmoment.gammaRatio_normalized_error_vertical s u
      (by rw [hsr]; norm_num) (by rw [hsi]; linarith)
      (by rw [hsi]; nlinarith [sq_nonneg ‖u‖, norm_nonneg u])
    apply hr.trans
    rw [hsi, div_le_iff₀ (by linarith : 0 < |y|)]
    nlinarith [sq_nonneg ‖u‖, norm_nonneg u]
  have hRupper : ‖R‖ ≤ 2 := by
    have h := norm_add_le (R-1) (1 : ℂ)
    have hh : R-1+1 = R := by ring
    rw [hh, norm_one] at h
    linarith
  have hRlower : 1/2 ≤ ‖R‖ := by
    have h := norm_sub_le R (R-1)
    have hh : R-(R-1) = 1 := by ring
    rw [hh, norm_one] at h
    linarith
  have hs0 : s ≠ 0 := by
    intro hs
    have h := congrArg Complex.re hs
    rw [hsr, Complex.zero_re] at h
    norm_num at h
  have hΓ0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hsr]; norm_num)
  have hp0 : s^u ≠ 0 := by simp [hs0]
  have hΓeq : Gamma (s+u) = R*s^u*Gamma s := by
    dsimp [R]
    field_simp
  have hnorm : ‖Gamma (s+u)‖ = ‖R‖*‖s^u‖*‖Gamma s‖ := by
    rw [hΓeq, norm_mul, norm_mul]
  have hsN : 1 ≤ ‖s‖ := by
    have h := Complex.abs_im_le_norm s
    rw [hsi] at h
    linarith
  have hsNu : ‖s‖ ≤ 1+|y| := by
    dsimp [s]
    exact (norm_add_le _ _).trans (by simp; linarith [abs_nonneg y])
  have hpN : ‖s^u‖ = ‖s‖^(σ-1/2) := by
    dsimp [u]
    exact Complex.norm_cpow_real _ _
  have hpupper : ‖s^u‖ ≤ ‖s‖ := by
    rw [hpN]
    simpa using Real.rpow_le_rpow_of_exponent_le hsN
      (show σ-1/2 ≤ 1 by linarith [hσ.2])
  have hplower : 1/‖s‖ ≤ ‖s^u‖ := by
    rw [hpN]
    simpa [Real.rpow_neg_one, one_div] using Real.rpow_le_rpow_of_exponent_le hsN
      (show (-1 : ℝ) ≤ σ-1/2 by linarith [hσ.1])
  rw [← hsu]
  change ‖Gamma (s+u)‖ ≤ 2*(1+|y|)*‖Gamma s‖ ∧
    ‖Gamma s‖ ≤ 2*(1+|y|)*‖Gamma (s+u)‖
  constructor
  · rw [hnorm]
    gcongr
    exact hpupper.trans hsNu
  · have hlo : (1/2)*(1/‖s‖)*‖Gamma s‖ ≤ ‖Gamma (s+u)‖ := by
      rw [hnorm]
      gcongr
    have hsNpos : 0 < ‖s‖ := zero_lt_one.trans_le hsN
    have hm := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2*‖s‖)
    have hid : (2*‖s‖)*((1/2)*(1/‖s‖)*‖Gamma s‖) = ‖Gamma s‖ := by
      field_simp
    rw [hid] at hm
    exact hm.trans (by gcongr)

private theorem gamma_strip_compact_weighted_bounds (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ y : ℝ, σ ∈ Icc (1/8 : ℝ) (7/8) → |y| ≤ M →
      ‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖*Real.exp (Real.pi*|y|/2) ≤ C ∧
      ‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖⁻¹*Real.exp (-(Real.pi*|y|/2)) ≤ C := by
  let K : Set (ℝ×ℝ) := Icc (1/8 : ℝ) (7/8) ×ˢ Icc (-M) M
  let γ : ℝ×ℝ → ℂ := fun p => Gamma ((p.1 : ℂ)+(p.2 : ℂ)*I)
  have hγ : ContinuousOn γ K := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply (Complex.continuousAt_Gamma _ ?_).comp
    · fun_prop
    · intro n hn
      have hr := congrArg Complex.re hn
      have hs : 1/8 ≤ p.1 := hp.1.1
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      simp at hr
      linarith
  have hγ0 : ∀ p ∈ K, ‖γ p‖ ≠ 0 := by
    intro p hp
    apply norm_ne_zero_iff.mpr
    apply Complex.Gamma_ne_zero_of_re_pos
    have hs : 1/8 ≤ p.1 := hp.1.1
    simp
    linarith
  let f : ℝ×ℝ → ℝ := fun p => ‖γ p‖*Real.exp (Real.pi*|p.2|/2)
  let g : ℝ×ℝ → ℝ := fun p => ‖γ p‖⁻¹*Real.exp (-(Real.pi*|p.2|/2))
  have hf : ContinuousOn f K := hγ.norm.mul (by fun_prop)
  have hg : ContinuousOn g K := (hγ.norm.inv₀ hγ0).mul (by fun_prop)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  obtain ⟨Cf,hCf⟩ := hK.bddAbove_image hf
  obtain ⟨Cg,hCg⟩ := hK.bddAbove_image hg
  refine ⟨max 0 (max Cf Cg), le_max_left _ _, ?_⟩
  intro σ y hσ hy
  have hp : (σ,y) ∈ K := ⟨hσ, abs_le.mp hy⟩
  constructor
  · exact (hCf (mem_image_of_mem f hp)).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hCg (mem_image_of_mem g hp)).trans
      ((le_max_right _ _).trans (le_max_right _ _))

theorem gamma_positive_strip_weighted_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ σ y : ℝ, σ ∈ Icc (1/8 : ℝ) (7/8) →
      ‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖*Real.exp (Real.pi*|y|/2) ≤ C*(1+|y|) ∧
      ‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖⁻¹*Real.exp (-(Real.pi*|y|/2)) ≤ C*(1+|y|) := by
  obtain ⟨C₀,hC₀,hbound⟩ := gamma_strip_compact_weighted_bounds 20
  let d : ℝ := min 1 Real.pi
  have hd : 0 < d := lt_min zero_lt_one Real.pi_pos
  let C : ℝ := max (C₀+1) (max (2*(2*Real.pi+1)) (2/d))
  have hC : 0 < C := lt_of_lt_of_le (by linarith : 0 < C₀+1) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro σ y hσ
  by_cases hy : |y| ≤ 20
  · have hb := hbound σ y hσ hy
    have hC₀C : C₀ ≤ C := (by linarith : C₀ ≤ C₀+1).trans (le_max_left _ _)
    have hCC : C ≤ C*(1+|y|) := le_mul_of_one_le_right hC.le (by linarith [abs_nonneg y])
    exact ⟨hb.1.trans (hC₀C.trans hCC), hb.2.trans (hC₀C.trans hCC)⟩
  · have hr := gamma_strip_large_relative σ y hσ (by linarith)
    have hh := gamma_half_weighted_norm_bounds y
    have hG : 0 < ‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖ := by
      apply norm_pos_iff.mpr
      apply Complex.Gamma_ne_zero_of_re_pos
      simp
      linarith [hσ.1]
    have hE : 0 < Real.exp (Real.pi*|y|/2) := Real.exp_pos _
    constructor
    · calc
        _ ≤ 2*(1+|y|)*(‖Gamma ((1/2 : ℂ)+(y : ℂ)*I)‖*
            Real.exp (Real.pi*|y|/2)) := by nlinarith [hr.1]
        _ ≤ 2*(1+|y|)*(2*Real.pi+1) := by
          gcongr
          exact hh.2
        _ ≤ C*(1+|y|) := by
          have hc : 2*(2*Real.pi+1) ≤ C :=
            (le_max_left _ _).trans (le_max_right _ _)
          nlinarith [abs_nonneg y]
    · have hlo : d ≤ 2*(1+|y|)*‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖*
          Real.exp (Real.pi*|y|/2) := by
        exact hh.1.trans (by nlinarith [hr.2])
      have hb : ‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖⁻¹*
          Real.exp (-(Real.pi*|y|/2)) ≤ (2/d)*(1+|y|) := by
        rw [Real.exp_neg]
        have he : ‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖⁻¹*
            (Real.exp (Real.pi*|y|/2))⁻¹ =
            1/(‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖*Real.exp (Real.pi*|y|/2)) := by
          ring
        rw [he, div_le_iff₀ (mul_pos hG hE)]
        calc
          1 ≤ (2*(1+|y|)*‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖*
              Real.exp (Real.pi*|y|/2))/d :=
            (le_div_iff₀ hd).mpr (by simpa only [one_mul] using hlo)
          _ = (2/d)*(1+|y|)*(‖Gamma ((σ : ℂ)+(y : ℂ)*I)‖*
              Real.exp (Real.pi*|y|/2)) := by ring
      exact hb.trans (by
        have hc : 2/d ≤ C := (le_max_right _ _).trans (le_max_right _ _)
        gcongr)

theorem gamma_positive_strip_envelopes :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc (1/8 : ℝ) (7/8) →
      ‖Gamma z‖ ≤ C*(1+|z.im|)*Real.exp (-(Real.pi*|z.im|/2)) ∧
      ‖Gamma z‖⁻¹ ≤ C*(1+|z.im|)*Real.exp (Real.pi*|z.im|/2) := by
  obtain ⟨C,hC,hbound⟩ := gamma_positive_strip_weighted_bounds
  refine ⟨C,hC,?_⟩
  intro z hz
  have he : (z.re : ℂ)+(z.im : ℂ)*I = z := by
    apply Complex.ext <;> simp
  have hb := hbound z.re z.im hz
  rw [he] at hb
  constructor
  · have h := mul_le_mul_of_nonneg_right hb.1
      (Real.exp_pos (-(Real.pi*|z.im|/2))).le
    simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using h
  · have h := mul_le_mul_of_nonneg_right hb.2
      (Real.exp_pos (Real.pi*|z.im|/2)).le
    simpa only [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] using h

end
end Sechstmoment.Source
