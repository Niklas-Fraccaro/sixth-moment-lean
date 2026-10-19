import Sechstmoment.Numerator.U.Replacement.GaussianTruncation

/-!
Logarithmic Mellin cutoffs for the actual Gaussian AFE. A cutoff proportional
to log T, unlike T^epsilon, can subsequently be used with one bound sequence
for all source derivative orders. This file proves the genuine tail estimate;
it does not assert source admissibility or the rectangular moment theorem.
-/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

/-- Gaussian decay at a positive logarithmic cutoff beats every prescribed
polynomial, with no assumed tail estimate. -/
theorem polynomial_gaussian_logarithmic_eventually_le {θ : ℝ} (hθ : 0 < θ)
    (q A : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      T^q * Real.exp (-(1/2)*(θ*Real.log T)^2) ≤ T^(-A) := by
  have hθsq : 0 < θ^2 := sq_pos_of_pos hθ
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (2*(q+A)/θ^2))),
    eventually_gt_atTop (0 : ℝ)] with T hL hT
  have hLpos : 0 < Real.log T := by
    linarith [(le_max_left (1 : ℝ) _).trans hL]
  have hlarge : 2*(q+A) ≤ θ^2*Real.log T := by
    have h := (le_max_right (1 : ℝ) _).trans hL
    simpa only [mul_comm] using (div_le_iff₀ hθsq).mp h
  rw [Real.rpow_def_of_pos hT, Real.rpow_def_of_pos hT, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hlarge hLpos.le]

/-- The actual V-tail has arbitrary power decay with cutoff theta log T.
The normalized pure-root separation is retained explicitly. -/
theorem bblrGaussianVTail_uniform_logarithmic_power_bound (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖ ≤ 1/4) → ∀ t ∈ Icc T (2*T), ∀ x : ℝ, 0 < x →
      ‖bblrGaussianVTail T σ α x t (θ*Real.log T)‖ ≤ C*T^(-(A : ℝ))/x := by
  obtain ⟨D,hD,hbound⟩ := bblrGaussianVTail_norm_le
  let E : ℝ := Real.exp 1*2^48*(1+1/δ^2)^24
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlog : ∀ᶠ T : ℝ in atTop, (Real.log T)^48 ≤ T := by
    have h := (log_pow_isLittleO_rpow 48 (δ := 1) zero_lt_one).bound zero_lt_one
    filter_upwards [h,eventually_gt_atTop (1 : ℝ)] with T hT hpos
    simpa only [Real.rpow_one,Real.norm_eq_abs,
      abs_of_pos (zero_lt_one.trans hpos),
      abs_of_nonneg (by positivity : 0 ≤ (Real.log T)^48),one_mul] using hT
  refine ⟨D*E*4^8,by positivity,?_⟩
  filter_upwards [hlog,polynomial_gaussian_logarithmic_eventually_le hθ 9 A,
    eventually_gt_atTop (1 : ℝ),Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with T hlog hdec hT hL
  intro σ hσ α hα t ht x hx
  have hCG : polarGaussianConstant T σ 1 ≤ E*T :=
    (polarGaussianConstant_log_growth hT hL hδ σ (hρ σ hσ)).trans
      (mul_le_mul_of_nonneg_left hlog hE)
  have htpos : 0 ≤ t := by linarith [ht.1]
  have htime : (2+t)^8 ≤ 4^8*T^8 := by
    rw [← mul_pow]
    gcongr
    linarith [ht.2]
  have hb := hbound T σ α hα t x (θ*Real.log T) htpos hx
    (mul_nonneg hθ.le (by linarith : 0 ≤ Real.log T))
  calc
    _ ≤ D*(E*T)*(4^8*T^8)/x*Real.exp (-(1/2)*(θ*Real.log T)^2) := by
      apply hb.trans
      gcongr
    _ = (D*E*4^8)/x*(T^9*Real.exp (-(1/2)*(θ*Real.log T)^2)) := by ring
    _ ≤ (D*E*4^8)/x*T^(-(A : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      convert hdec using 1; norm_num
    _ = _ := by ring

/-- The real fourfold AFE tail is controlled, not a free error function. -/
theorem bblrGaussianAFETail_uniform_logarithmic_power_bound (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖ ≤ 1/4) → ∀ t ∈ Icc T (2*T),
      ‖bblrGaussianAFETail T σ α t (θ*Real.log T)‖ ≤ C*T^(-(A : ℝ)) := by
  obtain ⟨D,hD,hbound⟩ :=
    bblrGaussianVTail_uniform_logarithmic_power_bound K δ hδ hρ hθ A
  let S : ℝ := ∑' n, bblrGaussianAFEQuadMajorant n
  have hS : 0 ≤ S := tsum_nonneg bblrGaussianAFEQuadMajorant_nonneg
  refine ⟨D*S,by positivity,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0 : ℝ)] with T hb hT
  intro σ hσ α hα t ht
  calc
    _ ≤ (D*T^(-(A : ℝ)))*S :=
      bblrGaussianAFETail_norm_le T σ α t (θ*Real.log T) hα (by positivity)
        (fun x hx => hb σ hσ α hα t ht x hx)
    _ = _ := by ring

/-- One bound works for all six actual shift tuples, including the dual one. -/
theorem bblrGaussianAFETail_uniform_logarithmic_six_shifts_bound
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ k : Fin 6,
      ∀ t ∈ Icc T (2*T),
      ‖bblrGaussianAFETail T σ (bblrSixShifts (rawMomentShifts T σ) k)
        t (θ*Real.log T)‖ ≤ C*T^(-(A : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ :=
    bblrGaussianAFETail_uniform_logarithmic_power_bound K δ hδ hρ hθ A
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num)] with T hb hs
  intro σ hσ k t ht
  apply hb σ hσ _ _ t ht
  intro j
  have h := hs σ hσ
  fin_cases k <;> fin_cases j <;> simp [bblrSixShifts] <;>
    first | simpa using h 0 | simpa using h 1 | simpa using h 2 | simpa using h 3

/-- Exact core-plus-tail reconstruction with the logarithmic cutoff. -/
theorem bblrGaussianAFE_logarithmic_truncation_six_shifts_error
    (K : Set MomentShifts) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {θ : ℝ} (hθ : 0 < θ) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ k : Fin 6,
      ∀ t ∈ Icc T (2*T),
      ‖bblrAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) k) t-
        bblrGaussianAFECore T σ (bblrSixShifts (rawMomentShifts T σ) k)
          t (θ*Real.log T)‖ ≤ C*T^(-(A : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ :=
    bblrGaussianAFETail_uniform_logarithmic_six_shifts_bound K hK δ hδ hρ hθ A
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num),eventually_gt_atTop (1 : ℝ)] with T hb hs hT
  intro σ hσ k t ht
  have hα : ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) k j‖ ≤ 1/4 := by
    intro j
    have h := hs σ hσ
    fin_cases k <;> fin_cases j <;> simp [bblrSixShifts] <;>
      first | simpa using h 0 | simpa using h 1 | simpa using h 2 | simpa using h 3
  rw [bblrGaussianAFE_core_add_tail T σ _ t (θ*Real.log T)
    (by linarith [ht.1]) (mul_nonneg hθ.le (Real.log_nonneg hT.le)) hα,
    add_sub_cancel_left]
  exact hb σ hσ k t ht

end
end Sechstmoment.Source
