import Sechstmoment.Denominator.Gram.PhaseExpansion
import Sechstmoment.Denominator.Unbalanced.CenteringPower

namespace Sechstmoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def d06ExtremeModelFourierSum (T : ℝ) (a : Fin 4 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (τ : ℂ) (Φ : ℝ → ℂ) : ℂ :=
  ∑ h∈d04ProfileBox T a,∑' n : ℕ × ℕ,
    d04OneSidedModelCoefficient T ρ σ h n*
      a03ProfileTimeFourier (d06ChiTimePowerProfile T Φ τ) T
        (d06OneSidedModelFrequency h n)

theorem d06ExtremeOneSidedMoment_fourier_identity {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R)
    {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2) :
    d06ExtremeOneSidedMoment T σ ρ Φ=d04CenteringPurePower T T (σ 0)*
      d06ExtremeModelFourierSum T a ρ σ (-σ 0/(Real.log T : ℂ))
        (fun y => (Φ y : ℂ)) := by
  have ht : 0<T := zero_lt_one.trans hT
  let τ : ℂ := -σ 0/(Real.log T : ℂ)
  let β : ℂ := d04CenteringPurePower T T (σ 0)
  let F : ℝ → ℂ := d06ChiTimePowerProfile T (fun y => (Φ y : ℂ)) τ
  have hΦC : ContDiff ℝ ∞ (fun y => (Φ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ
  have hΦCs : tsupport (fun y => (Φ y : ℂ))⊆Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦs
  have hFI : Integrable F := d06ChiTimePowerProfile_integrable T hΦC hΦCs τ
  have he : d06ExtremeOneSidedMoment T σ ρ Φ=
      β*(∫ t : ℝ,F (t/T)*d06AllPositiveAmplifier T t ρ*d04OneSidedCenteredPair T t σ) := by
    unfold d06ExtremeOneSidedMoment
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      by_cases hz : Φ (t/T)=0
      · simp [F,d06ChiTimePowerProfile,a03ProfileProduct,hz]
      · have hyp : 0<t/T := zero_lt_one.trans_le (hΦs (subset_tsupport Φ hz)).1
        have hf := d04CenteringPurePower_dyadic_factorization ht hyp (σ 0)
        rw [show T*(t/T)=t by field_simp] at hf
        rw [hf]
        dsimp [F,d06ChiTimePowerProfile,a03ProfileProduct,β,τ]
        rw [show T*(t/T)=t by field_simp]
        ring
  rw [he,d06OneSided_model_weighted_integral_identity hT hR (Real.log_pos hT)
    hRL a ρ hcap σ hσ F hFI]
  rfl

theorem d06ExtremeModelFourierSum_bound_of_frequency_bound {T R F D A : ℝ}
    (hT : 1<T) (hR : 0≤R) (hF : 0≤F) (hD : 0≤D)
    (hL : 0<Real.log T) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ j x,|ρ j x|≤F)
    (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R) (τ : ℂ) (Φ : ℝ → ℂ)
    (hfourier : ∀ h∈d04ProfileBox T a,∀ n : ℕ × ℕ,
      ‖a03ProfileTimeFourier (d06ChiTimePowerProfile T Φ τ) T
        (d06OneSidedModelFrequency h n)‖≤D*T^(-A)) :
    ‖d06ExtremeModelFourierSum T a ρ σ τ Φ‖≤
      (9*D*Real.exp R*F^4*2^4)*T^(6+(∑ j,a j)/2-A) := by
  have ht : 0<T := zero_lt_one.trans hT
  have hp := d04_exponential_coefficient_mass hT.le (Real.exp_pos R).le
    (d04OneSidedPairCoefficient T σ)
    (d04_oneSided_pair_coefficient_norm_le ht hR hL hRL σ hσ)
  have hc (h : Fin 4 → ℕ) : Summable (fun n => ‖d04OneSidedModelCoefficient T ρ σ h n‖) := by
    unfold d04OneSidedModelCoefficient
    simp_rw [norm_mul]
    exact hp.1.mul_left _
  have hm (h : Fin 4 → ℕ) :
      (∑' n : ℕ × ℕ,‖d04OneSidedModelCoefficient T ρ σ h n‖)≤
        ‖d04ProfileCoefficient T ρ h‖*(9*Real.exp R*T^6) := by
    unfold d04OneSidedModelCoefficient
    simp_rw [norm_mul]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hp.2 (norm_nonneg _)
  have hb (h : Fin 4 → ℕ) (hh : h∈d04ProfileBox T a) :
      ‖∑' n : ℕ × ℕ,d04OneSidedModelCoefficient T ρ σ h n*
        a03ProfileTimeFourier (d06ChiTimePowerProfile T Φ τ) T
          (d06OneSidedModelFrequency h n)‖≤
        (D*T^(-A))*(‖d04ProfileCoefficient T ρ h‖*(9*Real.exp R*T^6)) := by
    have hs : Summable (fun n : ℕ × ℕ => ‖d04OneSidedModelCoefficient T ρ σ h n*
        a03ProfileTimeFourier (d06ChiTimePowerProfile T Φ τ) T
          (d06OneSidedModelFrequency h n)‖) := by
      apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((hc h).mul_left (D*T^(-A)))
      intro n
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hfourier h hh n) (norm_nonneg _)).trans_eq (mul_comm _ _)
    calc
      _ ≤ ∑' n : ℕ × ℕ,‖d04OneSidedModelCoefficient T ρ σ h n*
          a03ProfileTimeFourier (d06ChiTimePowerProfile T Φ τ) T
            (d06OneSidedModelFrequency h n)‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n : ℕ × ℕ,(D*T^(-A))*‖d04OneSidedModelCoefficient T ρ σ h n‖ :=
        hs.tsum_le_tsum (fun n => by
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_left (hfourier h hh n) (norm_nonneg _)).trans_eq
            (mul_comm _ _)) ((hc h).mul_left _)
      _ = (D*T^(-A))*∑' n : ℕ × ℕ,‖d04OneSidedModelCoefficient T ρ σ h n‖ := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left (hm h) (by positivity)
  have hmass := d04ProfileCoefficient_mass_le ht hF a ρ hρ
  unfold d06ExtremeModelFourierSum
  calc
    _ ≤ ∑ h∈d04ProfileBox T a,‖∑' n : ℕ × ℕ,d04OneSidedModelCoefficient T ρ σ h n*
        a03ProfileTimeFourier (d06ChiTimePowerProfile T Φ τ) T
          (d06OneSidedModelFrequency h n)‖ := norm_sum_le _ _
    _ ≤ ∑ h∈d04ProfileBox T a,(D*T^(-A))*(‖d04ProfileCoefficient T ρ h‖*(9*Real.exp R*T^6)) :=
      Finset.sum_le_sum hb
    _ = (9*D*Real.exp R*T^6*T^(-A))*
        ∑ h∈d04ProfileBox T a,‖d04ProfileCoefficient T ρ h‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ ≤ (9*D*Real.exp R*T^6*T^(-A))*(F^4*2^4*T^((∑ j,a j)/2)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = (9*D*Real.exp R*F^4*2^4)*(T^6*T^(-A)*T^((∑ j,a j)/2)) := by ring
    _ = _ := by
      have he : T^6*T^(-A)*T^((∑ j,a j)/2)=T^(6+(∑ j,a j)/2-A) := by
        rw [show (T^6 : ℝ)=T^(6:ℝ) by norm_cast,
          ← Real.rpow_add ht,← Real.rpow_add ht]
        congr 1
        ring
      rw [he]

end
end Sechstmoment
