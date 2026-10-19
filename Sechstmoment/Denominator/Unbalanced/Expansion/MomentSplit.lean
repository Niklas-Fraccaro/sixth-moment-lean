import Sechstmoment.Denominator.Unbalanced.ActualOffDiagonal
import Sechstmoment.Denominator.Unbalanced.Expansion.DiagonalConnector

/-! Exact expansion and Bochner integration of the actual one-sided
centered series with its four literal profile Dirichlet sums. -/
namespace Sechstmoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d04UnbalancedAmplifier_pair_model_identity {T : ℝ} (hT : 1<T)
    (t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : Fin 2 → ℂ) :
    d04UnbalancedAmplifier T t ρ*d04OneSidedCenteredPair T t σ=
      ∑ h∈d04ProfileBox T a, ∑' n : ℕ × ℕ,
        d04OneSidedModelCoefficient T ρ σ h n*
          Complex.exp (((t*d04OneSidedModelFrequency h n : ℝ) : ℂ)*I) := by
  rw [d04UnbalancedAmplifier_finite_expansion hT t a ρ hcap,
    d04OneSidedCenteredPair_phase_identity,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← tsum_mul_left,d04ProfileTerm_phase_identity]
  apply tsum_congr
  intro n
  have hH : 0<(d04ProfileH h : ℝ) := by exact_mod_cast d04ProfileH_pos h
  have hK : 0<(d04ProfileK h : ℝ) := by exact_mod_cast d04ProfileK_pos h
  have hlog : d04OneSidedModelFrequency h n =
      Real.log ((d04ProfileK h : ℝ)/(d04ProfileH h : ℝ))+
        Real.log ((n.1+1 : ℝ)*(n.2+1 : ℝ)) := by
    unfold d04OneSidedModelFrequency
    push_cast
    rw [Real.log_div (by positivity) hH.ne',Real.log_div hK.ne' hH.ne',
      Real.log_mul (by positivity) hK.ne']
    ring
  have he : Complex.exp (((t*Real.log ((d04ProfileK h : ℝ)/(d04ProfileH h : ℝ)) : ℝ) : ℂ)*I)*
      Complex.exp (((t*Real.log ((n.1+1 : ℝ)*(n.2+1 : ℝ)) : ℝ) : ℂ)*I)=
      Complex.exp (((t*d04OneSidedModelFrequency h n : ℝ) : ℂ)*I) := by
    rw [← Complex.exp_add,hlog]
    congr 1
    push_cast
    ring
  unfold d04OneSidedModelCoefficient
  rw [← he]
  ring

theorem d04_scalar_phase_series_integrable {ι : Type*}
    (F : ℝ → ℂ) (hF : Integrable F) (c : ι → ℂ) (ℓ : ι → ℝ)
    (hc : Summable (fun i => ‖c i‖)) :
    Integrable (fun t : ℝ => F t*∑' i,c i*Complex.exp (((ℓ i*t : ℝ) : ℂ)*I)) := by
  have hn (i : ι) (t : ℝ) : ‖c i*Complex.exp (((ℓ i*t : ℝ) : ℂ)*I)‖=‖c i‖ := by
    rw [norm_mul,Complex.norm_exp]
    simp
  have hs : Continuous (fun t : ℝ => ∑' i,c i*Complex.exp (((ℓ i*t : ℝ) : ℂ)*I)) := by
    apply continuous_tsum (fun i => by fun_prop) hc
    exact fun i t => (hn i t).le
  apply (hF.norm.mul_const (∑' i,‖c i‖)).mono'
    (hF.aestronglyMeasurable.mul hs.aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    change ‖F t*(∑' i,c i*Complex.exp (((ℓ i*t : ℝ) : ℂ)*I))‖≤‖F t‖*(∑' i,‖c i‖)
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg (F t))
    calc
      _ ≤ ∑' i,‖c i*Complex.exp (((ℓ i*t : ℝ) : ℂ)*I)‖ :=
        norm_tsum_le_tsum_norm (by simpa only [hn] using hc)
      _ = _ := tsum_congr (fun i => hn i t)

theorem d04OneSided_model_weighted_integral_identity {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hL : 0<Real.log T) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R)
    (F : ℝ → ℂ) (hF : Integrable F) :
    (∫ t : ℝ,F (t/T)*d04UnbalancedAmplifier T t ρ*d04OneSidedCenteredPair T t σ)=
      ∑ h∈d04ProfileBox T a, ∑' n : ℕ × ℕ,
        d04OneSidedModelCoefficient T ρ σ h n*
          a03ProfileTimeFourier F T (d04OneSidedModelFrequency h n) := by
  have ht : 0<T := zero_lt_one.trans hT
  have hp := (d04_exponential_coefficient_mass hT.le (Real.exp_pos R).le
    (d04OneSidedPairCoefficient T σ)
    (d04_oneSided_pair_coefficient_norm_le ht hR hL hRL σ hσ)).1
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
  rw [he,integral_finsetSum _ (fun h _ => hi h)]
  apply Finset.sum_congr rfl
  intro h hh
  simpa only [mul_comm] using d04_oneSided_fourier_tsum F ht hF
    (d04OneSidedModelCoefficient T ρ σ h) (d04OneSidedModelFrequency h) (hcoeff h)

theorem d04_timePower_profile_regular {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1 : ℝ) 2) (τ : ℂ) :
    ContDiff ℝ ∞ (a03ProfileProduct Φ (fun y : ℝ => (y : ℂ)^τ)) ∧
      HasCompactSupport (a03ProfileProduct Φ (fun y : ℝ => (y : ℂ)^τ)) := by
  have hs := a03_profile_product_contDiff hΦ (fun y hy =>
    positive_cpow_contDiffAt τ (zero_lt_one.trans_le (hΦs hy).1))
  refine ⟨hs,?_⟩
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    ((a03_profile_product_tsupport _ _).trans hΦs)

theorem d04OneSidedModelFrequency_eq_zero_of_diagonal
    (h : Fin 4 → ℕ) (n : ℕ × ℕ) (hn : d04OneSidedModelDiagonal h n) :
    d04OneSidedModelFrequency h n=0 := by
  unfold d04OneSidedModelFrequency
  rw [show (n.1+1)*(n.2+1)*d04ProfileK h=d04ProfileH h from hn,
    div_self (by exact_mod_cast (d04ProfileH_pos h).ne'),Real.log_one]

theorem d04OneSided_model_timePower_diagonal_partition {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hL : 0<Real.log T) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1 : ℝ) 2) (τ : ℂ) :
    (∫ t : ℝ,Φ (t/T)*((t/T : ℝ) : ℂ)^τ*
      d04UnbalancedAmplifier T t ρ*d04OneSidedCenteredPair T t σ)=
      ((T : ℂ)*∫ y : ℝ,Φ y*(y : ℂ)^τ)*d04OneSidedModelDiagonalSum T a ρ σ+
        d04OneSidedModelOffDiagonal T a ρ σ τ Φ := by
  let F : ℝ → ℂ := a03ProfileProduct Φ (fun y : ℝ => (y : ℂ)^τ)
  have hF := d04_timePower_profile_regular hΦ hΦs τ
  have hFK : HasCompactSupport F := hF.2
  have hFS : ContDiff ℝ ∞ F := hF.1
  have hFI : Integrable F := hFS.continuous.integrable_of_hasCompactSupport hFK
  have hid := d04OneSided_model_weighted_integral_identity hT hR hL hRL
    a ρ hcap σ hσ F hFI
  change (∫ t : ℝ,F (t/T)*d04UnbalancedAmplifier T t ρ*d04OneSidedCenteredPair T t σ)=_
  rw [hid]
  have hp := (d04_exponential_coefficient_mass hT.le (Real.exp_pos R).le
    (d04OneSidedPairCoefficient T σ)
    (d04_oneSided_pair_coefficient_norm_le (zero_lt_one.trans hT) hR hL hRL σ hσ)).1
  have hcoeff (h : Fin 4 → ℕ) : Summable (fun n => ‖d04OneSidedModelCoefficient T ρ σ h n‖) := by
    unfold d04OneSidedModelCoefficient
    simp_rw [norm_mul]
    exact hp.mul_left _
  have hzero : a03ProfileTimeFourier F T 0=(T : ℂ)*∫ y : ℝ,Φ y*(y : ℂ)^τ := by
    rw [a03_profile_time_fourier_rescaling F (zero_lt_one.trans hT)]
    simp [profileLaplaceTransform,F,a03ProfileProduct]
  unfold d04OneSidedModelDiagonalSum d04OneSidedModelOffDiagonal
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  have hs := d04_summable_fourier_coefficients F hFK hFS (zero_lt_one.trans hT)
    (d04OneSidedModelCoefficient T ρ σ h) (d04OneSidedModelFrequency h) (hcoeff h)
  rw [d04_oneSided_exact_diagonal_partition _ hs (d04OneSidedModelDiagonal h)]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  split_ifs with hn
  · rw [d04OneSidedModelFrequency_eq_zero_of_diagonal h n hn,hzero]
    ring
  · simp

end
end Sechstmoment
