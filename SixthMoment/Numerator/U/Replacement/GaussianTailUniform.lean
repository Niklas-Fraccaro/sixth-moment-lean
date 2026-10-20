import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import SixthMoment.Analysis.Asymptotics.PowerLog
import SixthMoment.Numerator.U.Replacement.GaussianCoefficientGrowth
import SixthMoment.Numerator.U.Replacement.GaussianTail


namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

theorem polarGaussianConstant_log_growth {T δ : ℝ} (hT : 1 < T)
    (hL : 1 ≤ Real.log T) (hδ : 0 < δ) (σ : MomentShifts)
    (hρ : ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖) :
    polarGaussianConstant T σ 1 ≤
      (Real.exp 1*2^48*(1+1/δ^2)^24)*(Real.log T)^48 := by
  have hLsq : 1 ≤ (Real.log T)^2 := by nlinarith
  have hk (ρ : ℂ) : polarKillingCoefficient ρ = (ρ^2)⁻¹ := by
    by_cases h : ρ = 0 <;> simp [polarKillingCoefficient,h]
  unfold polarGaussianConstant
  simp only [hk, one_pow, abs_one, show (1+1 : ℝ) = 2 by norm_num]
  have hp : (∏ k : PurePolarIndex, (1+‖((purePolarRoot T σ k)^2)⁻¹‖)) ≤
      (1+1/δ^2)^24*(Real.log T)^48 := by
    calc
      _ ≤ ∏ _k : PurePolarIndex, ((1+1/δ^2)*(Real.log T)^2) := by
        apply Finset.prod_le_prod₀
        · intro k hk
          positivity
        · intro k hk
          have hi := purePolarRoot_inverse_sq_norm hT hδ σ k (hρ k)
          have he : (Real.log T)^2/δ^2 = (1/δ^2)*(Real.log T)^2 := by ring
          rw [he] at hi
          nlinarith
      _ = _ := by simp [PurePolarIndex,mul_pow,← pow_mul]
  calc
    _ ≤ (Real.exp 1*2^48)*((1+1/δ^2)^24*(Real.log T)^48) := by gcongr
    _ = _ := by ring

theorem compactNormalizedShifts_eventually_norm_small (K : Set MomentShifts)
    (hK : IsCompact K) (r : ℝ) (hr : 0 < r) :
    ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ j, ‖rawMomentShifts T σ j‖ ≤ r := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop (max B 0/r+1))] with T hT
  intro σ hσ j
  have hL : 0 < Real.log T := by
    have hm : 0 ≤ max B 0/r := div_nonneg (le_max_right _ _) hr.le
    linarith
  have hj : ‖σ j‖ ≤ max B 0 :=
    ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left B 0)
  simp only [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
  apply (div_le_iff₀ hL).mpr
  have hh := (div_lt_iff₀ hr).mp (by linarith : max B 0/r < Real.log T)
  linarith

theorem polynomial_gaussian_power_eventually_le {ε : ℝ} (hε : 0 < ε) (q A : ℝ) :
    ∀ᶠ T : ℝ in atTop, T^q*Real.exp (-(1/2)*(T^ε)^2) ≤ T^(-A) := by
  have hp : 0 < 2*ε := by linarith
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((q+A)/(2*ε)) (1/2) (by norm_num)).comp (tendsto_rpow_atTop hp)
  have he : (fun T : ℝ => (T^(2*ε))^((q+A)/(2*ε))*
      Real.exp (-(1/2)*(T^(2*ε)))) =ᶠ[atTop]
      (fun T : ℝ => T^(q+A)*Real.exp (-(1/2)*(T^ε)^2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have he₁ : (T^(2*ε))^((q+A)/(2*ε)) = T^(q+A) := by
      rw [← Real.rpow_mul hT.le]
      congr 1
      field_simp
    have he₂ : T^(2*ε) = (T^ε)^2 := by
      rw [← Real.rpow_natCast,← Real.rpow_mul hT.le]
      congr 1
      ring
    rw [he₁,he₂]
  have hlim' := hlim.congr' he
  filter_upwards [hlim'.eventually_le_const zero_lt_one,
    eventually_gt_atTop (0 : ℝ)] with T hbound hT
  have hpow : 0 < T^A := Real.rpow_pos_of_pos hT A
  rw [Real.rpow_neg hT.le,inv_eq_one_div]
  apply (le_div_iff₀ hpow).mpr
  have heq : (T^q*Real.exp (-(1/2)*(T^ε)^2))*T^A =
      T^(q+A)*Real.exp (-(1/2)*(T^ε)^2) := by
    rw [Real.rpow_add hT]
    ring
  rw [heq]
  exact hbound

theorem bblrGaussianVTail_uniform_power_bound (K : Set MomentShifts)
    (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ α : MomentShifts,
      (∀ j, ‖α j‖ ≤ 1/4) → ∀ t ∈ Icc T (2*T), ∀ x : ℝ, 0 < x →
      ‖bblrGaussianVTail T σ α x t (T^ε)‖ ≤ C*T^(-(A : ℝ))/x := by
  obtain ⟨D,hD,hbound⟩ := bblrGaussianVTail_norm_le
  let E : ℝ := Real.exp 1*2^48*(1+1/δ^2)^24
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlog : ∀ᶠ T : ℝ in atTop, (Real.log T)^48 ≤ T := by
    have h := (log_pow_isLittleO_rpow 48 (δ := 1) zero_lt_one).bound zero_lt_one
    filter_upwards [h,eventually_gt_atTop (1 : ℝ)] with T hT hpos
    simpa only [Real.rpow_one,Real.norm_eq_abs,
      abs_of_pos (zero_lt_one.trans hpos),abs_of_nonneg (by positivity : 0 ≤ (Real.log T)^48),
      one_mul] using hT
  refine ⟨D*E*4^8,by positivity,?_⟩
  filter_upwards [hlog,polynomial_gaussian_power_eventually_le hε 9 A,
    eventually_gt_atTop (1 : ℝ),Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (1 : ℝ))] with T hlog hdec hT hL
  intro σ hσ α hα t ht x hx
  have hCG : polarGaussianConstant T σ 1 ≤ E*T :=
    (polarGaussianConstant_log_growth hT hL hδ σ (hρ σ hσ)).trans
      (mul_le_mul_of_nonneg_left hlog hE)
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hp : (2+t)^8 ≤ 4^8*T^8 := by
    rw [← mul_pow]
    gcongr
    linarith [ht.2]
  have hCG0 := polarGaussianConstant_nonneg T σ 1
  calc
    _ ≤ D*polarGaussianConstant T σ 1*(2+t)^8/x*Real.exp (-(1/2)*(T^ε)^2) :=
      hbound T σ α hα t x (T^ε) ht0 hx (Real.rpow_pos_of_pos (by linarith) ε).le
    _ ≤ D*(E*T)*(4^8*T^8)/x*Real.exp (-(1/2)*(T^ε)^2) := by gcongr
    _ = (D*E*4^8)/x*(T^9*Real.exp (-(1/2)*(T^ε)^2)) := by ring
    _ ≤ (D*E*4^8)/x*T^(-(A : ℝ)) := by
      gcongr
      convert hdec using 1
      exact congrArg (fun q : ℝ => q*Real.exp (-(1/2)*(T^ε)^2))
        (Real.rpow_natCast T 9).symm
    _ = _ := by ring

theorem bblrGaussianVTail_uniform_raw_power_bound (K : Set MomentShifts)
    (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ ≤ ‖normalizedPurePolarRoot σ k‖)
    {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ t ∈ Icc T (2*T),
      ∀ x : ℝ, 0 < x →
      ‖bblrGaussianVTail T σ (rawMomentShifts T σ) x t (T^ε)‖ ≤
        C*T^(-(A : ℝ))/x := by
  obtain ⟨C,hC,hbound⟩ := bblrGaussianVTail_uniform_power_bound K δ hδ hρ hε A
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,compactNormalizedShifts_eventually_norm_small K hK (1/4)
    (by norm_num)] with T hb hs
  intro σ hσ t ht x hx
  exact hb σ hσ (rawMomentShifts T σ) (hs σ hσ) t ht x hx

end
end SixthMoment.Source
