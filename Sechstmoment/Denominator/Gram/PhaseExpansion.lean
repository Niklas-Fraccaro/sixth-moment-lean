import Sechstmoment.Denominator.Gram.PhaseDefinitions
import Sechstmoment.Denominator.Unbalanced.Expansion.MomentSplit

/-! The actual extreme-phase model has four positive amplifier indices.
Their product is at most `T^S`; every resulting pair frequency is at least
`-S log T`. The Dirichlet series remains unrestricted. -/
namespace Sechstmoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def d06ProfileProduct (h : Fin 4 → ℕ) : ℕ := ∏ j,(h j+1)

def d06ProfileTerm (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) (h : Fin 4 → ℕ) : ℂ :=
  ∏ j,(ρ j (Real.log (h j+1 : ℝ)/Real.log T) : ℂ)/
    (h j+1 : ℂ)^(criticalLinePoint t)

def d06OneSidedModelFrequency (h : Fin 4 → ℕ) (n : ℕ × ℕ) : ℝ :=
  Real.log (((n.1+1 : ℝ)*(n.2+1 : ℝ))/(d06ProfileProduct h : ℝ))

def d06ChiTimePowerProfile (T : ℝ) (Φ : ℝ → ℂ) (τ : ℂ) (y : ℝ) : ℂ :=
  a03ProfileProduct Φ (fun y : ℝ => (y : ℂ)^τ) y*(criticalChi (T*y))⁻¹

theorem d06ChiTimePowerProfile_integrable (T : ℝ) {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc (1:ℝ) 2) (τ : ℂ) :
    Integrable (d06ChiTimePowerProfile T Φ τ) := by
  obtain ⟨hs,hk⟩ := d04_timePower_profile_regular hΦ hΦs τ
  have hc : Continuous (d06ChiTimePowerProfile T Φ τ) :=
    hs.continuous.mul (d04_criticalChi_inv_continuous.comp (by fun_prop))
  exact hc.integrable_of_hasCompactSupport hk.mul_right

theorem d06ProfileProduct_pos (h : Fin 4 → ℕ) : 0<d06ProfileProduct h := by
  unfold d06ProfileProduct
  apply Finset.prod_pos
  intro j _
  omega

theorem d06AllPositiveAmplifier_finite_expansion {T : ℝ} (hT : 1<T)
    (t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) :
    d06AllPositiveAmplifier T t ρ=∑ h∈d04ProfileBox T a,d06ProfileTerm T t ρ h := by
  unfold d06AllPositiveAmplifier
  simp_rw [profileDirichletSum_eq_finite hT _ _ (hcap _) _]
  unfold d04ProfileBox d02PositiveBox d06ProfileTerm
  exact Finset.prod_univ_sum _ _

theorem d06ProfileTerm_phase_identity (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (h : Fin 4 → ℕ) :
    d06ProfileTerm T t ρ h=d04ProfileCoefficient T ρ h*
      Complex.exp (((-t*Real.log (d06ProfileProduct h : ℝ) : ℝ) : ℂ)*I) := by
  have hs (j : Fin 4) : (h j+1 : ℂ)=((h j+1 : ℝ) : ℂ) := by push_cast; rfl
  have hp (j : Fin 4) (r : ℂ) :
      r/((h j+1 : ℝ) : ℂ)^(criticalLinePoint t)=
        (r*((h j+1 : ℝ) : ℂ)^(-(1/2 : ℂ)))*
          Complex.exp (((-t*Real.log (h j+1 : ℝ) : ℝ) : ℂ)*I) :=
    d04_positive_profile_factor_phase (by positivity) r t
  unfold d06ProfileTerm d04ProfileCoefficient
  simp_rw [hs,hp]
  rw [Finset.prod_mul_distrib,← Complex.exp_sum]
  congr 1
  have hlog : Real.log (d06ProfileProduct h : ℝ)=∑ j,Real.log (h j+1 : ℝ) := by
    unfold d06ProfileProduct
    push_cast
    exact Real.log_prod (fun _ _ => by positivity)
  rw [hlog]
  push_cast
  rw [Finset.mul_sum,Finset.sum_mul]

theorem d06ProfileProduct_cap {T : ℝ} (hT : 0<T) (a : Fin 4 → ℝ)
    (h : Fin 4 → ℕ) (hh : h∈d04ProfileBox T a) :
    (d06ProfileProduct h : ℝ)≤T^(∑ j,a j) := by
  have hj (j : Fin 4) : (h j+1 : ℝ)≤T^(a j) := by
    have hn : h j+1≤⌊T^(a j)⌋₊ := Nat.succ_le_of_lt
      (Finset.mem_range.1 (Fintype.mem_piFinset.1 hh j))
    have hn' : (h j+1 : ℝ)≤(⌊T^(a j)⌋₊ : ℝ) := by exact_mod_cast hn
    exact hn'.trans (Nat.floor_le (Real.rpow_nonneg hT.le _))
  unfold d06ProfileProduct
  push_cast
  calc
    _ ≤ ∏ j,T^(a j) := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => hj j)
    _ = _ := (Real.rpow_sum_of_pos hT a Finset.univ).symm

theorem d06OneSidedModelFrequency_lower_bound {T : ℝ} (hT : 1<T)
    (a : Fin 4 → ℝ) (h : Fin 4 → ℕ) (hh : h∈d04ProfileBox T a) (n : ℕ × ℕ) :
    -(∑ j,a j)*Real.log T≤d06OneSidedModelFrequency h n := by
  have hT0 : 0<T := zero_lt_one.trans hT
  have hH : 0<(d06ProfileProduct h : ℝ) := by exact_mod_cast d06ProfileProduct_pos h
  have hN : 1≤(n.1+1 : ℝ)*(n.2+1 : ℝ) := by
    nlinarith [(Nat.cast_nonneg n.1 : (0:ℝ)≤n.1),(Nat.cast_nonneg n.2 : (0:ℝ)≤n.2)]
  have hln : 0≤Real.log ((n.1+1 : ℝ)*(n.2+1 : ℝ)) := Real.log_nonneg hN
  have hlH := Real.log_le_log hH (d06ProfileProduct_cap hT0 a h hh)
  rw [Real.log_rpow hT0] at hlH
  unfold d06OneSidedModelFrequency
  rw [Real.log_div (by positivity) hH.ne']
  linarith

theorem d06AllPositiveAmplifier_pair_model_identity {T : ℝ} (hT : 1<T)
    (t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : Fin 2 → ℂ) :
    d06AllPositiveAmplifier T t ρ*d04OneSidedCenteredPair T t σ=
      ∑ h∈d04ProfileBox T a,∑' n : ℕ × ℕ,
        d04OneSidedModelCoefficient T ρ σ h n*
          Complex.exp (((t*d06OneSidedModelFrequency h n : ℝ) : ℂ)*I) := by
  rw [d06AllPositiveAmplifier_finite_expansion hT t a ρ hcap,
    d04OneSidedCenteredPair_phase_identity,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  rw [← tsum_mul_left,d06ProfileTerm_phase_identity]
  apply tsum_congr
  intro n
  have hH : 0<(d06ProfileProduct h : ℝ) := by exact_mod_cast d06ProfileProduct_pos h
  have hlog : d06OneSidedModelFrequency h n=
      -Real.log (d06ProfileProduct h : ℝ)+Real.log ((n.1+1 : ℝ)*(n.2+1 : ℝ)) := by
    unfold d06OneSidedModelFrequency
    rw [Real.log_div (by positivity) hH.ne']
    ring
  have he : Complex.exp (((-t*Real.log (d06ProfileProduct h : ℝ) : ℝ) : ℂ)*I)*
      Complex.exp (((t*Real.log ((n.1+1 : ℝ)*(n.2+1 : ℝ)) : ℝ) : ℂ)*I)=
      Complex.exp (((t*d06OneSidedModelFrequency h n : ℝ) : ℂ)*I) := by
    rw [← Complex.exp_add,hlog]
    congr 1
    push_cast
    ring
  unfold d04OneSidedModelCoefficient
  rw [← he]
  ring

theorem d06OneSided_model_weighted_integral_identity {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hL : 0<Real.log T) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R)
    (F : ℝ → ℂ) (hF : Integrable F) :
    (∫ t : ℝ,F (t/T)*d06AllPositiveAmplifier T t ρ*d04OneSidedCenteredPair T t σ)=
      ∑ h∈d04ProfileBox T a,∑' n : ℕ × ℕ,
        d04OneSidedModelCoefficient T ρ σ h n*
          a03ProfileTimeFourier F T (d06OneSidedModelFrequency h n) := by
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
        Complex.exp (((t*d06OneSidedModelFrequency h n : ℝ) : ℂ)*I)) := by
    simpa only [mul_comm] using d04_scalar_phase_series_integrable
      _ hFscale (d04OneSidedModelCoefficient T ρ σ h) (d06OneSidedModelFrequency h) (hcoeff h)
  have he : (fun t : ℝ => F (t/T)*d06AllPositiveAmplifier T t ρ*d04OneSidedCenteredPair T t σ)=
      fun t : ℝ => ∑ h∈d04ProfileBox T a,F (t/T)*∑' n : ℕ × ℕ,
        d04OneSidedModelCoefficient T ρ σ h n*
          Complex.exp (((t*d06OneSidedModelFrequency h n : ℝ) : ℂ)*I) := by
    funext t
    calc
      _ = F (t/T)*(d06AllPositiveAmplifier T t ρ*d04OneSidedCenteredPair T t σ) := by ring
      _ = F (t/T)*∑ h∈d04ProfileBox T a,∑' n : ℕ × ℕ,
          d04OneSidedModelCoefficient T ρ σ h n*
            Complex.exp (((t*d06OneSidedModelFrequency h n : ℝ) : ℂ)*I) := by
        rw [d06AllPositiveAmplifier_pair_model_identity hT t a ρ hcap σ]
      _ = _ := Finset.mul_sum ..
  rw [he,integral_finsetSum _ (fun h _ => hi h)]
  apply Finset.sum_congr rfl
  intro h _
  simpa only [mul_comm] using d04_oneSided_fourier_tsum F ht hF
    (d04OneSidedModelCoefficient T ρ σ h) (d06OneSidedModelFrequency h) (hcoeff h)

theorem d06OneSided_model_weighted_integrable {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : Fin 2 → ℂ) (hσ : ∀ j,‖σ j‖≤R)
    (F : ℝ → ℂ) (hF : Integrable F) :
    Integrable (fun t : ℝ => F (t/T)*d06AllPositiveAmplifier T t ρ*d04OneSidedCenteredPair T t σ) := by
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
        Complex.exp (((t*d06OneSidedModelFrequency h n : ℝ) : ℂ)*I)) := by
    simpa only [mul_comm] using d04_scalar_phase_series_integrable
      _ hFscale (d04OneSidedModelCoefficient T ρ σ h) (d06OneSidedModelFrequency h) (hcoeff h)
  have he : (fun t : ℝ => F (t/T)*d06AllPositiveAmplifier T t ρ*d04OneSidedCenteredPair T t σ)=
      fun t : ℝ => ∑ h∈d04ProfileBox T a,F (t/T)*∑' n : ℕ × ℕ,
        d04OneSidedModelCoefficient T ρ σ h n*
          Complex.exp (((t*d06OneSidedModelFrequency h n : ℝ) : ℂ)*I) := by
    funext t
    calc
      _ = F (t/T)*(d06AllPositiveAmplifier T t ρ*d04OneSidedCenteredPair T t σ) := by ring
      _ = F (t/T)*∑ h∈d04ProfileBox T a,∑' n : ℕ × ℕ,
          d04OneSidedModelCoefficient T ρ σ h n*
            Complex.exp (((t*d06OneSidedModelFrequency h n : ℝ) : ℂ)*I) := by
        rw [d06AllPositiveAmplifier_pair_model_identity hT t a ρ hcap σ]
      _ = _ := Finset.mul_sum ..
  rw [he]
  exact integrable_finsetSum _ (fun h _ => hi h)

end
end Sechstmoment
