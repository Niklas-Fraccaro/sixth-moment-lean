import Sechstmoment.Numerator.U.ZeroModes.Ratio.SourceMomentFrontJoin
import Sechstmoment.Numerator.U.ZeroModes.Ratio.SourceUniformMoment
import Sechstmoment.Numerator.U.ZeroModes.RatioUnitTail

/-! Broad actual kernel bounds for the ratio-source complement. Arbitrary
ratio power tails pay for the literal finite grids and Mellin integration. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_amplified_time_kernel_uniform_polynomial
    {a b c κ θ R : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j,‖α j‖≤1/4) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual : Bool,∀ u w : ℕ,∀ n : Fin 4→ℕ,
      ‖∫ t : ℝ,rectangularMomentPairWeight T f g Φ u w t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤C*T^(4:ℝ) := by
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 := (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨C0,hC0,hb0⟩ := a03_gaussian_frequency_logarithmic_uniform_derivative_bounds
    hΦc hΦs hc hc1 (by linarith : 2*c<(3:ℝ)) hκ hθ (by norm_num : (0:ℝ)≤1/4)
  obtain ⟨C1,hC1,hb1⟩ := a03_gaussian_dual_frequency_logarithmic_uniform_derivative_bounds
    hΦc hΦs hc hc1 (by linarith : 2*c<(3:ℝ)) hκ hθ (by norm_num : (0:ℝ)≤1/4) hR
  let C := F*G*(C0 0 0+C1 0 0)
  refine ⟨C,mul_nonneg (mul_nonneg hF hG) (add_nonneg (hC0 0 0) (hC1 0 0)),?_⟩
  filter_upwards [hb0,hb1,eventually_gt_atTop (1:ℝ)] with T hb0 hb1 hT
  intro σ α hσ hα hroot v hv dual u w n
  have hTp : 0<T := zero_lt_one.trans hT
  have hstatic := a03ActualMellinStaticFactor_norm_le hF hG hc.le T f g hfb hgb α hα u w n v
  have hfreq0 := (hb0 σ α hα hroot v hv).2 0 0 (-T*Real.log (phaseActualProductRatio (u+1) (w+1) n))
  have hfreq1 := (hb1 σ α hσ hα hroot v hv).2 0 0 (-T*Real.log (phaseActualProductRatio (u+1) (w+1) n))
  simp only [pow_zero,one_mul,iteratedDeriv_zero] at hfreq0 hfreq1
  have hpow : T*T^(3:ℝ)=T^(4:ℝ) := by
    calc
      _=T^(1:ℝ)*T^(3:ℝ) := by rw [Real.rpow_one]
      _=T^(4:ℝ) := by rw [show (4:ℝ)=(1:ℝ)+3 by norm_num,Real.rpow_add hTp]
  cases dual
  · simp only [Bool.false_eq_true,ite_false,mul_one]
    rw [a03_actual_amplified_mellin_time_factorization,
      a03_gaussian_actual_time_exact_rescaling _ hTp _ _ _ (by omega) (by omega),
      norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hTp.le]
    calc
      _≤(F*G)*(T*(C0 0 0*T^(3:ℝ))) := mul_le_mul hstatic
        (mul_le_mul_of_nonneg_left hfreq0 hTp.le) (mul_nonneg hTp.le (norm_nonneg _)) (mul_nonneg hF hG)
      _=(F*G*C0 0 0)*T^(4:ℝ) := by rw [←hpow]; ring
      _≤C*T^(4:ℝ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith [hC1 0 0] : C0 0 0≤C0 0 0+C1 0 0) (mul_nonneg hF hG))
        (Real.rpow_nonneg hTp.le _)
  · simp only [ite_true]
    rw [a03_actual_amplified_dual_mellin_time_factorization,
      a03_gaussian_actual_dual_time_exact_rescaling _ hTp _ _ _ (by omega) (by omega),
      norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hTp.le]
    calc
      _≤(F*G)*(T*(C1 0 0*T^(3:ℝ))) := mul_le_mul hstatic
        (mul_le_mul_of_nonneg_left hfreq1 hTp.le) (mul_nonneg hTp.le (norm_nonneg _)) (mul_nonneg hF hG)
      _=(F*G*C1 0 0)*T^(4:ℝ) := by rw [←hpow]; ring
      _≤C*T^(4:ℝ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith [hC0 0 0] : C1 0 0≤C0 0 0+C1 0 0) (mul_nonneg hF hG))
        (Real.rpow_nonneg hTp.le _)

theorem a03_actual_ratio_partition_uniform_linear_bound {κ : ℝ} (hκ : 0<κ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) → ∀ x : ℝ,0<x →
      ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) x‖≤C*T := by
  let B := 1+gaussianTailConstant 4/(2*Real.pi)*(Real.exp 1*16*(1+1/κ^2)^2)
  let L := (Nat.factorial 4:ℝ)*Real.exp 1
  have hB : 0≤B := by
    dsimp [B]
    exact add_nonneg zero_le_one (mul_nonneg (div_nonneg (gaussianTailConstant_nonneg 4) (by positivity)) (by positivity))
  refine ⟨B*L,mul_nonneg hB (by dsimp [L]; positivity),?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hT hlog
  intro σ hroot x hx
  rw [a03ZeroModeRatioPartition_eq_logDerivative _ hx]
  have hg := a03ZeroModeRatioLogDerivative_global_log_growth hT hlog hκ σ hroot 0 (Real.log x)
  have hl : (Real.log T)^4≤L*T := by
    apply (pow_le_pow_left₀ (by linarith : 0≤Real.log T) (by linarith : Real.log T≤1+Real.log T) 4).trans
    simpa only [Real.rpow_one,one_pow,div_one] using logarithmic_power_le_rpow (by norm_num : (0:ℝ)<1) hT.le 4
  exact hg.trans (by simpa only [B,mul_assoc] using mul_le_mul_of_nonneg_left hl hB)

theorem a03_actual_ratio_pair_weight_uniform_rapid {κ γ A : ℝ}
    (hκ : 0<κ) (hγ : 0<γ) (hA : 0<A) (M : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ x y : ℝ,0<x → 0<y → (A*T^γ≤x ∨ A*T^γ≤y) →
      ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) x*
        a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) y‖≤C*T^(-(M:ℝ)) := by
  obtain ⟨C,hC,hsmall⟩ := a03ActualRatioPartition_uniform_polynomial_tail hκ hγ hA (M+1)
  obtain ⟨D,hD,hbound⟩ := a03_actual_ratio_partition_uniform_linear_bound hκ
  refine ⟨C*D,mul_nonneg hC hD,?_⟩
  filter_upwards [hsmall,hbound,eventually_gt_atTop (1:ℝ)] with T hs hb hT
  intro σ hroot x y hx hy hlarge
  have hpow : T^(-((M+1:ℕ):ℝ))*T=T^(-(M:ℝ)) := by
    calc
      _=T^(-((M+1:ℕ):ℝ))*T^(1:ℝ) := by rw [Real.rpow_one]
      _=T^(-((M+1:ℕ):ℝ)+1) := (Real.rpow_add (zero_lt_one.trans hT) _ _).symm
      _=T^(-(M:ℝ)) := by congr 1; push_cast; ring
  rw [norm_mul]
  rcases hlarge with hxlarge|hylarge
  · calc
      _≤(C*T^(-((M+1:ℕ):ℝ)))*(D*T) := mul_le_mul (hs σ hroot x hxlarge) (hb σ hroot y hy) (norm_nonneg _) (by positivity)
      _=(C*D)*T^(-(M:ℝ)) := by rw [show (C*T^(-((M+1:ℕ):ℝ)))*(D*T)=(C*D)*(T^(-((M+1:ℕ):ℝ))*T) by ring,hpow]
  · calc
      _≤(D*T)*(C*T^(-((M+1:ℕ):ℝ))) := mul_le_mul (hb σ hroot x hx) (hs σ hroot y hylarge) (norm_nonneg _) (by positivity)
      _=(C*D)*T^(-(M:ℝ)) := by rw [show (D*T)*(C*T^(-((M+1:ℕ):ℝ)))=(C*D)*(T^(-((M+1:ℕ):ℝ))*T) by ring,hpow]

end
end Sechstmoment
