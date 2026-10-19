import Sechstmoment.Denominator.Unbalanced.Expansion.PhysicalSplit

/-! Time integrability of the actual one-sided moment follows from the
proved exponential absolute mass and the literal finite profile expansion. -/
namespace Sechstmoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d04OneSided_model_weighted_integrable {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R)
    (F : ℝ → ℂ) (hF : Integrable F) :
    Integrable (fun t : ℝ => F (t/T)*d04UnbalancedAmplifier T t ρ*d04OneSidedCenteredPair T t σ) := by
  have ht : 0<T := zero_lt_one.trans hT
  have hp := (d04_exponential_coefficient_mass hT.le (Real.exp_pos R).le
    (d04OneSidedPairCoefficient T σ)
    (d04_oneSided_pair_coefficient_norm_le ht hR (Real.log_pos hT) hRL σ hσ)).1
  have hcoeff (h : Fin 4 → ℕ) : Summable (fun n => ‖d04OneSidedModelCoefficient T ρ σ h n‖) := by
    unfold d04OneSidedModelCoefficient
    simp_rw [norm_mul]
    exact hp.mul_left _
  have hFscale : Integrable (fun t : ℝ => F (t/T)) :=
    (integrable_comp_div_iff F ht.ne').2 hF
  have hi (h : Fin 4 → ℕ) : Integrable (fun t : ℝ => F (t/T)*∑' n : ℕ × ℕ,
      d04OneSidedModelCoefficient T ρ σ h n*
        Complex.exp (((t*d04OneSidedModelFrequency h n : ℝ) : ℂ)*I)) := by
    simpa only [mul_comm] using d04_scalar_phase_series_integrable
      _ hFscale (d04OneSidedModelCoefficient T ρ σ h) (d04OneSidedModelFrequency h) (hcoeff h)
  have he : (fun t : ℝ => F (t/T)*d04UnbalancedAmplifier T t ρ*d04OneSidedCenteredPair T t σ)=
      fun t : ℝ => ∑ h∈d04ProfileBox T a,F (t/T)*∑' n : ℕ × ℕ,
        d04OneSidedModelCoefficient T ρ σ h n*
          Complex.exp (((t*d04OneSidedModelFrequency h n : ℝ) : ℂ)*I) := by
    funext t
    calc
      _ = F (t/T)*(d04UnbalancedAmplifier T t ρ*d04OneSidedCenteredPair T t σ) := by ring
      _ = F (t/T)*∑ h∈d04ProfileBox T a, ∑' n : ℕ × ℕ,
          d04OneSidedModelCoefficient T ρ σ h n*
            Complex.exp (((t*d04OneSidedModelFrequency h n : ℝ) : ℂ)*I) := by
        rw [d04UnbalancedAmplifier_pair_model_identity hT t a ρ hcap σ]
      _ = _ := Finset.mul_sum ..
  rw [he]
  exact integrable_finsetSum _ (fun h _ => hi h)

theorem d04OneSidedShiftedIntegrand_integrable_on_shiftBox {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hRL : 2*R≤Real.log T)
    (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1 : ℝ) 2)
    (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R) :
    Integrable (fun t : ℝ => (Φ (t/T) : ℂ)*d04CenteringPurePower T t (σ 0)*
      d04OneSidedCenteredPair T t σ*d04UnbalancedAmplifier T t ρ) := by
  have ht : 0<T := zero_lt_one.trans hT
  let τ : ℂ := d04OneSidedTimeExponent T (σ 0)
  let β : ℂ := d04CenteringPurePower T T (σ 0)
  let F : ℝ → ℂ := a03ProfileProduct (fun y => (Φ y : ℂ)) (fun y : ℝ => (y : ℂ)^τ)
  have hΦC : ContDiff ℝ ∞ (fun y => (Φ y : ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ
  have hΦCs : tsupport (fun y => (Φ y : ℂ))⊆Icc (1 : ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦs
  have hFreg := d04_timePower_profile_regular hΦC hΦCs τ
  have hFI : Integrable F := hFreg.1.continuous.integrable_of_hasCompactSupport hFreg.2
  have hcap : ∀ j x,a j<x → ρ j x=0 := by
    intro j x hx
    by_contra hn
    exact (not_lt_of_ge (hρs j (subset_tsupport (ρ j) hn)).2) hx
  have hi := (d04OneSided_model_weighted_integrable hT hR hRL a ρ hcap σ hσ F hFI).const_mul β
  apply hi.congr
  exact Eventually.of_forall fun t => by
    dsimp only
    by_cases hz : Φ (t/T)=0
    · simp [F,a03ProfileProduct,hz]
    · have hyp : 0<t/T := zero_lt_one.trans_le (hΦs (subset_tsupport Φ hz)).1
      have he := d04CenteringPurePower_dyadic_factorization ht hyp (σ 0)
      rw [show T*(t/T)=t by field_simp] at he
      rw [he]
      dsimp [F,a03ProfileProduct,β,τ,d04OneSidedTimeExponent]
      ring

theorem d04OneSidedShiftedIntegrand_eventually_integrable_on_shiftBox
    (R : ℝ) (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1 : ℝ) 2) :
    ∀ᶠ T : ℝ in atTop,∀ σ : Fin 2 → ℂ,(∀ j,‖σ j‖≤R) →
      Integrable (fun t : ℝ => (Φ (t/T) : ℂ)*d04CenteringPurePower T t (σ 0)*
        d04OneSidedCenteredPair T t σ*d04UnbalancedAmplifier T t ρ) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (2*R))] with T hT hRL
  intro σ hσ
  have hR : 0≤R := (norm_nonneg (σ 0)).trans (hσ 0)
  exact d04OneSidedShiftedIntegrand_integrable_on_shiftBox hT hR hRL ρ a hρs Φ hΦ hΦs σ hσ

end
end Sechstmoment
