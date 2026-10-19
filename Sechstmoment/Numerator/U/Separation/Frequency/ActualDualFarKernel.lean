import Sechstmoment.Numerator.U.Separation.Frequency.ActualFarKernel
import Sechstmoment.Numerator.U.Separation.Frequency.GammaDualFar

/-! The far estimate is applied to the literal amplified Mellin AFE kernel,
with its exact static arithmetic factor retained in the error budget. -/
namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem a03_actual_amplified_dual_mellin_time_factorization (T : ℝ)
    (f g Φ : ℝ → ℝ) (σ α : MomentShifts) (u v : ℕ) (n : Fin 4 → ℕ) (z : ℂ) :
    (∫ t : ℝ, rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t (rawMomentShifts T σ)*
      rectangularAFEMellinKernel (polarPoleKiller T σ) α t n z)=
      a03ActualMellinStaticFactor T f g α u v n z*
        a03GaussianActualDualTimeIntegral (fun x => (Φ x:ℂ)) T σ α z (u+1) (v+1) n := by
  unfold a03GaussianActualDualTimeIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold rectangularAFEMellinKernel a03ActualMellinStaticFactor
  simp only [div_eq_mul_inv]
  calc
    _ = (rectangularMomentPairWeight T f g Φ u v t*rectangularAFEOscillation t n)*
        (polarPoleKiller T σ z*z⁻¹*bblrGammaQuotient t α z*(Real.pi:ℂ)^(-2*z))*
        (∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z))⁻¹*bblrDualMultiplier t (rawMomentShifts T σ) := by ring
    _ = _ := by
      rw [rectangular_actual_pair_weight_oscillation]
      unfold phaseActualAmplifierPairConstant
      ring

theorem a03_actual_amplified_all_far_dual_kernel_uniform_rapid
    {Φ : ℝ → ℝ} (hΦ : SmoothDyadicWeight Φ)
    {c ε κ θ A R ρ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hA : 0≤A) (hR : 0≤R) (hρ : 0<ρ) (hρ1 : ρ≤1) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤A) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ f g : ℝ → ℝ, ∀ positive : Bool,
      ∀ u w : ℕ, ∀ n : Fin 4 → ℕ,
      (if positive then rectangularPositiveQuadGap (u+1) (w+1) n
        else rectangularNegativeQuadGap (u+1) (w+1) n) →
      T^(ρ-1)*Real.sqrt ((u+1:ℝ)*(w+1)*(n 0+1)*(n 1+1)*(n 2+1)*(n 3+1))≤
        (rectangularAFEGap positive (u+1) (w+1) n:ℝ) →
      ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*bblrDualMultiplier t (rawMomentShifts T σ)*
        rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤
        ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖*C*T^(-M) := by
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ))⊆Icc 1 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  obtain ⟨C,hC,hb⟩ := a03_gaussian_all_far_dual_uniform_rapid hΦc hΦs hc hc1 hε hκ hθ hA hR hρ hρ1 M
  refine ⟨C,hC,?_⟩
  filter_upwards [hb] with T hT
  intro σ α hσ hα hroot v hv f g positive u w n hn hfar
  rw [a03_actual_amplified_dual_mellin_time_factorization,norm_mul]
  exact (mul_le_mul_of_nonneg_left
    (hT σ α hσ hα hroot v hv positive (u+1) (w+1) (by omega) (by omega) n hn
      (by simpa only [Nat.cast_add,Nat.cast_one] using hfar)) (norm_nonneg _)).trans_eq (by ring)

end
end Sechstmoment
