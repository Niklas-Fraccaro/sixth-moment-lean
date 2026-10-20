import Sechstmoment.Zeta.Gamma.StirlingTail


namespace Sechstmoment.Source
open Complex Real Filter
open scoped BigOperators Topology
noncomputable section

def gammaStirlingMain (s : ℂ) : ℂ :=
  (Real.sqrt (2*Real.pi):ℂ)*Complex.exp ((s-1/2)*Complex.log s-s)

theorem gammaStirlingFactor_uniform_error (s : ℂ) (hs : 0 < s.re) (him : 16 ≤ |s.im|) :
    ‖gammaStirlingFactor s/(Real.sqrt (2*Real.pi):ℂ)-1‖ ≤ 16/|s.im| := by
  let S : ℂ := (Real.sqrt (2*Real.pi):ℂ)
  let δ := 16/|s.im|
  let E := fun n : ℕ => Complex.exp (∑ k ∈ Finset.range n, stirlingStepError (s+k))
  have ht0 : 0 < |s.im| := by linarith
  have hS : S ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*Real.pi)).ne'
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hE (n : ℕ) : ‖E n-1‖ ≤ δ := by
    have H := stirlingStepError_finite_sum_bound s hs.le (by linarith) n
    have hsmall : ‖∑ k ∈ Finset.range n, stirlingStepError (s+k)‖ ≤ 1 :=
      H.trans ((div_le_one ht0).mpr (by linarith))
    apply (Complex.norm_exp_sub_one_le hsmall).trans
    apply (mul_le_mul_of_nonneg_left H (by norm_num)).trans_eq
    dsimp only [δ]
    ring
  have hEnorm (n : ℕ) : ‖E n‖ ≤ 1+δ := by
    have H := norm_sub_le (E n-1) (-1:ℂ)
    simp only [sub_neg_eq_add,sub_add_cancel,norm_neg,norm_one] at H
    linarith [hE n]
  have hbound (n : ℕ) : ‖gammaStirlingFactor s/S-1‖ ≤
      ‖gammaStirlingFactor (s+(n:ℂ))/S-1‖*(1+δ)+δ := by
    have he : gammaStirlingFactor s/S-1 =
        (gammaStirlingFactor (s+(n:ℂ))/S-1)*E n+(E n-1) := by
      rw [gammaStirlingFactor_iterate s hs n]
      dsimp only [E]
      ring
    rw [he]
    calc
      _ ≤ ‖(gammaStirlingFactor (s+(n:ℂ))/S-1)*E n‖+‖E n-1‖ := norm_add_le _ _
      _ = ‖gammaStirlingFactor (s+(n:ℂ))/S-1‖*‖E n‖+‖E n-1‖ := by rw [norm_mul]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hEnorm n) (norm_nonneg _)) (hE n)
  have htail : Tendsto (fun n : ℕ => ‖gammaStirlingFactor (s+(n:ℂ))/S-1‖)
      atTop (𝓝 0) := by
    have H := (((gammaStirlingFactor_tendsto s hs).div_const S).sub_const 1).norm
    change Tendsto (fun n : ℕ => ‖gammaStirlingFactor (s+(n:ℂ))/S-1‖)
      atTop (𝓝 ‖S/S-1‖) at H
    simpa only [div_self hS,sub_self,norm_zero] using H
  have hlim : Tendsto (fun n : ℕ =>
      ‖gammaStirlingFactor (s+(n:ℂ))/S-1‖*(1+δ)+δ) atTop (𝓝 δ) := by
    simpa only [zero_mul,zero_add] using (htail.mul_const (1+δ)).add_const δ
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall hbound)

theorem gamma_stirling_relative_error (s : ℂ) (hs : 0 < s.re) (him : 16 ≤ |s.im|) :
    ‖Complex.Gamma s/gammaStirlingMain s-1‖ ≤ 16/|s.im| := by
  have hS : (Real.sqrt (2*Real.pi):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*Real.pi)).ne'
  have hid : Complex.Gamma s/gammaStirlingMain s =
      gammaStirlingFactor s/(Real.sqrt (2*Real.pi):ℂ) := by
    unfold gammaStirlingMain gammaStirlingFactor
    rw [show s-(s-1/2)*Complex.log s = -((s-1/2)*Complex.log s-s) by ring,
      Complex.exp_neg]
    field_simp [hS]
  rw [hid]
  exact gammaStirlingFactor_uniform_error s hs him

theorem gamma_stirling_absolute_error (s : ℂ) (hs : 0 < s.re) (him : 16 ≤ |s.im|) :
    ‖Complex.Gamma s-gammaStirlingMain s‖ ≤ ‖gammaStirlingMain s‖*(16/|s.im|) := by
  have hmain : gammaStirlingMain s ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (by positivity : (0:ℝ) < 2*Real.pi)).ne')
    (Complex.exp_ne_zero _)
  have H := gamma_stirling_relative_error s hs him
  rw [div_sub_one hmain,norm_div] at H
  simpa only [mul_comm] using (div_le_iff₀ (norm_pos_iff.mpr hmain)).mp H

end
end Sechstmoment.Source
