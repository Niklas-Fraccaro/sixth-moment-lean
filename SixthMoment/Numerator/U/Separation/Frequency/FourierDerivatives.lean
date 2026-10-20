import Mathlib.Analysis.Complex.RealDeriv
import SixthMoment.Analysis.Fourier.ProfileProduct
import SixthMoment.Numerator.U.Diagonal.ProfileHolomorphy

namespace SixthMoment
open Complex Real MeasureTheory Set
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def a03FrequencyWeightedProfile (f : ℝ → ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  ((x : ℂ) * I) ^ k * f x

theorem a03_frequency_weighted_profile_tsupport (f : ℝ → ℂ) (k : ℕ) :
    tsupport (a03FrequencyWeightedProfile f k) ⊆ tsupport f :=
  tsupport_mul_subset_right

theorem a03_frequency_weighted_profile_contDiff {f : ℝ → ℂ}
    (hS : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (a03FrequencyWeightedProfile f k) := by
  unfold a03FrequencyWeightedProfile
  exact ((Complex.ofRealCLM.contDiff.mul contDiff_const).pow k).mul hS

private theorem frequency_first_deriv {f : ℝ → ℂ}
    (hK : HasCompactSupport f) (hC : Continuous f) (ξ : ℝ) :
    deriv (fun ξ : ℝ => profileLaplaceTransform f ((ξ : ℂ) * I)) ξ =
      profileLaplaceTransform (a03FrequencyWeightedProfile f 1) ((ξ : ℂ) * I) := by
  have hp := (profileLaplaceTransform_hasDerivAt hK hC ((ξ : ℂ) * I)).comp ξ
    (Complex.ofRealCLM.hasDerivAt.mul_const I)
  have he : (∫ x : ℝ, Complex.exp (((ξ : ℂ) * I) * (x : ℂ)) *
      (x : ℂ) * f x) * I =
      profileLaplaceTransform (a03FrequencyWeightedProfile f 1) ((ξ : ℂ) * I) := by
    rw [← integral_mul_const]
    unfold profileLaplaceTransform
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [a03FrequencyWeightedProfile, pow_one]
    ring
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul, he] using hp.deriv

theorem a03_profile_frequency_derivative_formula {f : ℝ → ℂ}
    (hK : HasCompactSupport f) (hS : ContDiff ℝ ∞ f) (k : ℕ) :
    iteratedDeriv k (fun ξ : ℝ => profileLaplaceTransform f ((ξ : ℂ) * I)) =
      fun ξ : ℝ => profileLaplaceTransform (a03FrequencyWeightedProfile f k) ((ξ : ℂ) * I) := by
  induction k with
  | zero =>
    have he : a03FrequencyWeightedProfile f 0 = f := by
      funext x
      simp [a03FrequencyWeightedProfile]
    simp only [iteratedDeriv_zero, he]
  | succ k hk =>
    rw [iteratedDeriv_succ, hk]
    funext ξ
    have hKk : HasCompactSupport (a03FrequencyWeightedProfile f k) :=
      hK.of_isClosed_subset (isClosed_tsupport _) (a03_frequency_weighted_profile_tsupport f k)
    rw [frequency_first_deriv hKk (a03_frequency_weighted_profile_contDiff hS k).continuous]
    congr 1
    funext x
    simp only [a03FrequencyWeightedProfile, pow_succ]
    ring

theorem a03_profile_frequency_derivatives_integral_bound {f : ℝ → ℂ}
    (hK : HasCompactSupport f) (hS : ContDiff ℝ ∞ f) (k N : ℕ) (ξ : ℝ) :
    |ξ| ^ N *
      ‖iteratedDeriv k (fun ξ : ℝ => profileLaplaceTransform f ((ξ : ℂ) * I)) ξ‖ ≤
      ∫ x : ℝ, ‖iteratedDeriv N (a03FrequencyWeightedProfile f k) x‖ := by
  rw [a03_profile_frequency_derivative_formula hK hS k]
  exact a03_profile_frequency_derivative_integral
    (hK.of_isClosed_subset (isClosed_tsupport _) (a03_frequency_weighted_profile_tsupport f k))
    (a03_frequency_weighted_profile_contDiff hS k) N ξ

theorem a03_profile_product_uniform_frequency_derivatives {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ ⊆ Icc 1 2) (k : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ A : ℝ → ℂ,
      (∀ x ∈ Icc (1 : ℝ) 2, ContDiffAt ℝ ∞ A x) →
      ∀ B : ℕ → ℝ, (∀ j, 0 ≤ B j) → ∀ D : ℝ, 0 ≤ D →
      (∀ j x, x ∈ Icc (1 : ℝ) 2 → ‖iteratedDeriv j A x‖ ≤ B j * D) →
      ∀ N : ℕ, ∀ ξ : ℝ,
      |ξ| ^ N * ‖iteratedDeriv k (fun ξ : ℝ =>
        profileLaplaceTransform (a03ProfileProduct Φ A) ((ξ : ℂ) * I)) ξ‖ ≤
        a03ProfileProductDerivativeBudget C B N * D := by
  obtain ⟨C, hC, hb⟩ := a03_profile_product_uniform_frequency_bound
    (a03_frequency_weighted_profile_contDiff hΦ k)
    ((a03_frequency_weighted_profile_tsupport Φ k).trans hs)
  refine ⟨C, hC, ?_⟩
  intro A hA B hB D hD hAd N ξ
  have hKA : HasCompactSupport (a03ProfileProduct Φ A) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      ((a03_profile_product_tsupport Φ A).trans hs)
  rw [a03_profile_frequency_derivative_formula hKA
    (a03_profile_product_contDiff hΦ (fun x hx => hA x (hs hx))) k]
  have he : a03FrequencyWeightedProfile (a03ProfileProduct Φ A) k =
      a03ProfileProduct (a03FrequencyWeightedProfile Φ k) A := by
    funext x
    simp only [a03FrequencyWeightedProfile, a03ProfileProduct]
    ring
  rw [he]
  exact hb A hA B hB D hD hAd N ξ

theorem a03_profile_product_all_frequency_derivatives {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ ⊆ Icc 1 2) :
    ∃ C : ℕ → ℕ → ℝ, (∀ k j, 0 ≤ C k j) ∧ ∀ A : ℝ → ℂ,
      (∀ x ∈ Icc (1 : ℝ) 2, ContDiffAt ℝ ∞ A x) →
      ∀ B : ℕ → ℝ, (∀ j, 0 ≤ B j) → ∀ D : ℝ, 0 ≤ D →
      (∀ j x, x ∈ Icc (1 : ℝ) 2 → ‖iteratedDeriv j A x‖ ≤ B j * D) →
      ∀ k N : ℕ, ∀ ξ : ℝ,
      |ξ| ^ N * ‖iteratedDeriv k (fun ξ : ℝ =>
        profileLaplaceTransform (a03ProfileProduct Φ A) ((ξ : ℂ) * I)) ξ‖ ≤
        a03ProfileProductDerivativeBudget (C k) B N * D := by
  choose C hC hb using fun k : ℕ => a03_profile_product_uniform_frequency_derivatives hΦ hs k
  refine ⟨C, hC, ?_⟩
  intro A hA B hB D hD hAd k N ξ
  exact hb k A hA B hB D hD hAd N ξ

end
end SixthMoment
