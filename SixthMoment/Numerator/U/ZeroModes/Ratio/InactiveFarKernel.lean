import SixthMoment.Numerator.U.ZeroModes.Ratio.BadSourceKernel

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_actual_ratio_inactive_far_time_kernel_uniform_rapid
    {a b c κ θ R s : ℝ} {f g Φ : ℝ→ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hs : 0<s) (hs1 : s≤1) (M : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual positive : Bool,
      ∀ p q : ℕ,∀ n : Fin 4→ℕ,a03ActualFarSelection T s positive p q n →
      ‖∫ t : ℝ,rectangularMomentPairWeight T f g Φ p q t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤C*T^(-M) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨C₀,hC₀,hb₀⟩ := a03_actual_amplified_all_far_kernel_uniform_rapid
    hΦ hc hc1 (show 2*c<2*c+1 by linarith) hκ hθ (by norm_num : (0:ℝ)≤1/4) hs hs1 M
  obtain ⟨C₁,hC₁,hb₁⟩ := a03_actual_amplified_all_far_dual_kernel_uniform_rapid
    hΦ hc hc1 (show 2*c<2*c+1 by linarith) hκ hθ (by norm_num : (0:ℝ)≤1/4) hR hs hs1 M
  let C : ℝ := F*G*(C₀+C₁)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hb₀,hb₁,eventually_ge_atTop (1:ℝ)] with T hb₀ hb₁ hT
  intro σ α hσ hα hroot v hv dual positive p q n hfar
  have hstatic := a03ActualMellinStaticFactor_norm_le hF hG hc.le T f g hfb hgb α hα p q n v
  have hb : ‖a03ActualMellinStaticFactor T f g α p q n ((c:ℂ)+(v:ℂ)*I)‖*
      (C₀+C₁)*T^(-M)≤C*T^(-M) := by
    dsimp [C]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hstatic (add_nonneg hC₀ hC₁)) (Real.rpow_nonneg (zero_le_one.trans hT) _)
  cases dual
  · simp only [Bool.false_eq_true,ite_false,mul_one]
    exact (hb₀ σ α hα hroot v hv f g positive p q n hfar.1 hfar.2).trans
      ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hC₁) (norm_nonneg _))
        (Real.rpow_nonneg (zero_le_one.trans hT) _)).trans hb)
  · simp only [ite_true]
    exact (hb₁ σ α hσ hα hroot v hv f g positive p q n hfar.1 hfar.2).trans
      ((mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hC₀) (norm_nonneg _))
        (Real.rpow_nonneg (zero_le_one.trans hT) _)).trans hb)

end
end SixthMoment
