import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Stirling
import SixthMoment.Zeta.Gamma.StirlingRecurrence


namespace SixthMoment.Source
open Complex Real Filter
open scoped Topology BigOperators
noncomputable section

theorem gamma_shift_product (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    Complex.Gamma (s+(N:ℂ)) = Complex.Gamma s*
      (∏ k ∈ Finset.range N, (s+(k:ℂ))) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hsn : s+(n:ℂ) ≠ 0 := by
      intro h
      have H := congrArg Complex.re h
      simp only [add_re,natCast_re,zero_re] at H
      have hn := Nat.cast_nonneg (α := ℝ) n
      linarith
    rw [Nat.cast_succ,show s+((n:ℂ)+1) = (s+n)+1 by ring,
      Complex.Gamma_add_one _ hsn,ih,Finset.prod_range_succ]
    ring

theorem gammaSeq_shift_product (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    Complex.GammaSeq s n*Complex.Gamma (s+((n+1:ℕ):ℂ)) =
      Complex.Gamma s*((n:ℂ)^s*(Nat.factorial n:ℂ)) := by
  have hp : (∏ k ∈ Finset.range (n+1), (s+(k:ℂ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk h
    have H := congrArg Complex.re h
    simp only [add_re,natCast_re,zero_re] at H
    have hn := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [gamma_shift_product s hs (n+1),Complex.GammaSeq]
  field_simp [hp]

def stirlingTailExponent (s : ℂ) (n : ℕ) : ℂ :=
  ((n:ℂ)+s+1/2)*Complex.log (1+(s+1)/(n:ℂ))-(s+1)

theorem stirlingTailExponent_tendsto (s : ℂ) :
    Tendsto (stirlingTailExponent s) atTop (𝓝 0) := by
  have hiR : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (n:ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_inv,Complex.ofReal_natCast,
      Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hiR
  have hfrac : Tendsto (fun n : ℕ => (s+1)/(n:ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using (tendsto_const_nhds (x := s+1)).mul hi
  have harg : Tendsto (fun n : ℕ => 1+(s+1)/(n:ℂ)) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1:ℂ))).add hfrac
  have hlog : Tendsto (fun n : ℕ => Complex.log (1+(s+1)/(n:ℂ))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.log_one] using!
      (Complex.hasDerivAt_log (by simp : (1:ℂ) ∈ Complex.slitPlane)).continuousAt.tendsto.comp harg
  have hlinear : Tendsto (fun n : ℕ => (n:ℂ)*((s+1)/(n:ℂ))) atTop (𝓝 (s+1)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop (0:ℕ)] with n hn
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
    field_simp [hnC]
  have hmain := Complex.tendsto_nat_mul_log_one_add_of_tendsto hlinear
  have H := (hmain.add ((tendsto_const_nhds (x := s+1/2)).mul hlog)).sub
    (tendsto_const_nhds (x := s+1))
  have heq : stirlingTailExponent s = fun n : ℕ =>
      (n:ℂ)*Complex.log (1+(s+1)/(n:ℂ))+
        (s+1/2)*Complex.log (1+(s+1)/(n:ℂ))-(s+1) := by
    funext n
    unfold stirlingTailExponent
    ring
  rw [heq]
  simpa only [mul_zero,add_zero,sub_self] using H

theorem real_stirlingSeq_exp_identity {n : ℕ} (hn : 0 < n) :
    Stirling.stirlingSeq n*Real.sqrt 2 =
      (Nat.factorial n:ℝ)*Real.exp ((n:ℝ)-((n:ℝ)+1/2)*Real.log n) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have hpow : ((n:ℝ)/Real.exp 1)^n = Real.exp ((Real.log n-1)*(n:ℝ)) := by
    rw [← Real.rpow_natCast,Real.rpow_def_of_pos (div_pos hnR (Real.exp_pos 1)),
      Real.log_div hnR.ne' (Real.exp_ne_zero 1),Real.log_exp]
  have hsqrt : Real.sqrt (n:ℝ) = Real.exp (Real.log n/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hnR]
    congr 1
    ring
  unfold Stirling.stirlingSeq
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),hsqrt,hpow,mul_assoc,← Real.exp_add]
  calc
    _ = (Nat.factorial n:ℝ)/Real.exp (Real.log n/2+(Real.log n-1)*(n:ℝ)) := by
      field_simp [hs2]
    _ = (Nat.factorial n:ℝ)*Real.exp (-(Real.log n/2+(Real.log n-1)*(n:ℝ))) := by
      rw [div_eq_mul_inv,← Real.exp_neg]
    _ = _ := by congr 1; congr 1; ring

theorem gammaStirlingFactor_tail_identity (s : ℂ) (hs : 0 < s.re) {n : ℕ} (hn : 0 < n) :
    gammaStirlingFactor (s+((n+1:ℕ):ℂ)) =
      (Complex.Gamma s/Complex.GammaSeq s n)*
        (((Stirling.stirlingSeq n:ℝ):ℂ)*(Real.sqrt 2:ℂ)*
          Complex.exp (-stirlingTailExponent s n)) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : (∏ k ∈ Finset.range (n+1), (s+(k:ℂ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk h
    have H := congrArg Complex.re h
    simp only [add_re,natCast_re,zero_re] at H
    have hkn := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hpow : (n:ℂ)^s ≠ 0 := by simp [Complex.cpow_eq_zero_iff,hnC]
  have hfac : (Nat.factorial n:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hseq : Complex.GammaSeq s n ≠ 0 := by
    unfold Complex.GammaSeq
    exact div_ne_zero (mul_ne_zero hpow hfac) hp
  have hshift0 : s+((n+1:ℕ):ℂ) ≠ 0 := by
    intro h
    have H := congrArg Complex.re h
    simp only [add_re,natCast_re,zero_re] at H
    have hkn := Nat.cast_nonneg (α := ℝ) (n+1)
    linarith
  have he : (n:ℂ)*(1+(s+1)/(n:ℂ)) = s+((n+1:ℕ):ℂ) := by
    push_cast
    field_simp [hnC]
    ring
  have harg0 : 1+(s+1)/(n:ℂ) ≠ 0 := by
    intro h
    have H := congrArg (fun z : ℂ => (n:ℂ)*z) h
    rw [he,mul_zero] at H
    exact hshift0 H
  have hlog := Complex.log_ofReal_mul hnR harg0
  simp only [Complex.ofReal_natCast] at hlog
  rw [he] at hlog
  have hlogn : Complex.log (n:ℂ) = (Real.log (n:ℝ):ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnR.le).symm
  have hreal := congrArg Complex.ofReal (real_stirlingSeq_exp_identity hn)
  push_cast at hreal
  have hgamma : Complex.Gamma (s+((n+1:ℕ):ℂ)) =
      Complex.Gamma s*((n:ℂ)^s*(Nat.factorial n:ℂ))/Complex.GammaSeq s n := by
    apply (eq_div_iff hseq).mpr
    rw [mul_comm]
    exact gammaSeq_shift_product s hs n
  have hnorm : (n:ℂ)^s*(Nat.factorial n:ℂ)*
      Complex.exp ((s+((n+1:ℕ):ℂ))-
        ((s+((n+1:ℕ):ℂ))-1/2)*Complex.log (s+((n+1:ℕ):ℂ))) =
      ((Stirling.stirlingSeq n:ℝ):ℂ)*(Real.sqrt 2:ℂ)*
        Complex.exp (-stirlingTailExponent s n) := by
    rw [hreal,Complex.cpow_def_of_ne_zero hnC,hlogn,hlog]
    have hmerge (a b F : ℂ) : Complex.exp a*F*Complex.exp b = F*Complex.exp (a+b) := by
      rw [Complex.exp_add]
      ring
    rw [hmerge,mul_assoc,← Complex.exp_add]
    congr 1
    congr 1
    unfold stirlingTailExponent
    push_cast
    ring
  unfold gammaStirlingFactor
  rw [hgamma]
  calc
    _ = (Complex.Gamma s/Complex.GammaSeq s n)*
        ((n:ℂ)^s*(Nat.factorial n:ℂ)*Complex.exp ((s+((n+1:ℕ):ℂ))-
          ((s+((n+1:ℕ):ℂ))-1/2)*Complex.log (s+((n+1:ℕ):ℂ)))) := by ring
    _ = _ := by rw [hnorm]

theorem gammaStirlingFactor_tendsto (s : ℂ) (hs : 0 < s.re) :
    Tendsto (fun n : ℕ => gammaStirlingFactor (s+(n:ℂ))) atTop
      (𝓝 (Real.sqrt (2*Real.pi):ℂ)) := by
  have hG : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    have H := congrArg Complex.re h
    simp only [neg_re,natCast_re] at H
    have hm := Nat.cast_nonneg (α := ℝ) m
    linarith
  have hratio : Tendsto (fun n : ℕ => Complex.Gamma s/Complex.GammaSeq s n) atTop (𝓝 1) := by
    simpa only [Pi.div_apply,div_self hG] using!
      (tendsto_const_nhds (x := Complex.Gamma s)).div (Complex.GammaSeq_tendsto_Gamma s) hG
  have hseq : Tendsto (fun n : ℕ => (Stirling.stirlingSeq n:ℂ)) atTop
      (𝓝 (Real.sqrt Real.pi:ℂ)) := by
    exact (Complex.continuous_ofReal.tendsto (Real.sqrt Real.pi)).comp
      Stirling.tendsto_stirlingSeq_sqrt_pi
  have hexp : Tendsto (fun n : ℕ => Complex.exp (-stirlingTailExponent s n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def,neg_zero,Complex.exp_zero] using!
      (Complex.continuous_exp.tendsto (-0:ℂ)).comp (stirlingTailExponent_tendsto s).neg
  have hroot : (Real.sqrt Real.pi:ℂ)*(Real.sqrt 2:ℂ) = (Real.sqrt (2*Real.pi):ℂ) := by
    have H : Real.sqrt Real.pi*Real.sqrt 2 = Real.sqrt (2*Real.pi) := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      ring
    exact_mod_cast H
  have H := hratio.mul ((hseq.mul (tendsto_const_nhds (x := (Real.sqrt 2:ℂ)))).mul hexp)
  have H' : Tendsto (fun n : ℕ =>
      (Complex.Gamma s/Complex.GammaSeq s n)*
        ((Stirling.stirlingSeq n:ℂ)*(Real.sqrt 2:ℂ)*Complex.exp (-stirlingTailExponent s n)))
      atTop (𝓝 (Real.sqrt (2*Real.pi):ℂ)) := by
    simpa only [mul_one,one_mul,hroot] using H
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  apply H'.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact (gammaStirlingFactor_tail_identity s hs hn).symm

end
end SixthMoment.Source
