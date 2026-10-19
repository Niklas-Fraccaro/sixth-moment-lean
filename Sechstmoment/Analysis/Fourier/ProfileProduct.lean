import Sechstmoment.Analysis.Fourier.UniformDecay
import Sechstmoment.Arithmetic.QuadraticDivisor.Definitions

/-! Fixed dyadic profiles localize a varying analytic amplitude. Genuine
derivative envelopes imply uniform integration by parts; no Fourier estimate
is assumed. Smoothness outside the profile support is not required. -/
namespace Sechstmoment
open Complex Real Source MeasureTheory Set
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def a03ProfileProduct (Φ A : ℝ → ℂ) (x : ℝ) : ℂ := Φ x*A x

theorem a03_profile_derivative_bounds {Φ : ℝ → ℂ}
    (hK : HasCompactSupport Φ) (hS : ContDiff ℝ ∞ Φ) :
    ∃ B : ℕ → ℝ, (∀ j, 0≤B j) ∧ ∀ j x, ‖iteratedDeriv j Φ x‖≤B j := by
  have hex (j : ℕ) : ∃ C : ℝ, ∀ x, ‖iteratedDeriv j Φ x‖≤C := by
    have hKj : HasCompactSupport (iteratedDeriv j Φ) :=
      hK.of_isClosed_subset (isClosed_tsupport _) (a03_iteratedDeriv_tsupport_subset Φ j)
    exact hKj.exists_bound_of_continuous (hS.continuous_iteratedDeriv j (by simp))
  choose C hC using hex
  refine ⟨fun j => max (C j) 0,fun j => le_max_right _ _,?_⟩
  intro j x
  exact (hC j x).trans (le_max_left _ _)

theorem a03_profile_product_contDiff {Φ A : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ)
    (hA : ∀ x∈tsupport Φ, ContDiffAt ℝ ∞ A x) :
    ContDiff ℝ ∞ (a03ProfileProduct Φ A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈tsupport Φ
  · exact hΦ.contDiffAt.mul (hA x hx)
  · have he : a03ProfileProduct Φ A =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport Φ).isOpen_compl.mem_nhds hx] with y hy
      have hz : Φ y=0 := Function.notMem_support.mp (fun hs => hy (subset_tsupport Φ hs))
      simp [a03ProfileProduct,hz]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem a03_profile_product_tsupport (Φ A : ℝ → ℂ) :
    tsupport (a03ProfileProduct Φ A)⊆tsupport Φ :=
  tsupport_mul_subset_left

def a03ProfileProductDerivativeBudget (C B : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i∈Finset.range (N+1), (N.choose i:ℝ)*C i*B (N-i)

theorem a03_profile_product_derivative_bound {Φ A : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    (hA : ∀ x∈Icc (1:ℝ) 2, ContDiffAt ℝ ∞ A x)
    {C B : ℕ → ℝ} (hC : ∀ j, 0≤C j) (hB : ∀ j, 0≤B j)
    (hΦd : ∀ j x, ‖iteratedDeriv j Φ x‖≤C j)
    {D : ℝ} (hD : 0≤D)
    (hAd : ∀ j x, x∈Icc (1:ℝ) 2 → ‖iteratedDeriv j A x‖≤B j*D) (N : ℕ) (x : ℝ) :
    ‖iteratedDeriv N (a03ProfileProduct Φ A) x‖≤a03ProfileProductDerivativeBudget C B N*D := by
  have hbudget : 0≤a03ProfileProductDerivativeBudget C B N := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hB (N-i))
  by_cases hx : x∈tsupport Φ
  · have hxI := hs hx
    rw [show a03ProfileProduct Φ A=fun x => Φ x*A x from rfl,
      iteratedDeriv_fun_mul (hΦ.contDiffAt.of_le (by simp)) ((hA x hxI).of_le (by simp))]
    calc
      _ ≤ ∑ i∈Finset.range (N+1), ‖(N.choose i:ℂ)*iteratedDeriv i Φ x*iteratedDeriv (N-i) A x‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i∈Finset.range (N+1), (N.choose i:ℝ)*C i*(B (N-i)*D) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [norm_mul,Complex.norm_natCast]
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hΦd i x) (Nat.cast_nonneg _)
        · exact hAd (N-i) x hxI
        · exact norm_nonneg _
        · exact mul_nonneg (Nat.cast_nonneg _) (hC i)
      _ = a03ProfileProductDerivativeBudget C B N*D := by
        unfold a03ProfileProductDerivativeBudget
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
  · have hz : iteratedDeriv N (a03ProfileProduct Φ A) x=0 := by
      apply Function.notMem_support.mp
      intro hnonzero
      exact hx (a03_profile_product_tsupport Φ A
        (a03_iteratedDeriv_tsupport_subset (a03ProfileProduct Φ A) N (subset_tsupport _ hnonzero)))
    rw [hz,norm_zero]
    exact mul_nonneg hbudget hD

theorem a03_profile_product_uniform_frequency_bound {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2) :
    ∃ C : ℕ → ℝ, (∀ j, 0≤C j) ∧ ∀ A : ℝ → ℂ,
      (∀ x∈Icc (1:ℝ) 2, ContDiffAt ℝ ∞ A x) →
      ∀ B : ℕ → ℝ, (∀ j, 0≤B j) → ∀ D : ℝ, 0≤D →
      (∀ j x, x∈Icc (1:ℝ) 2 → ‖iteratedDeriv j A x‖≤B j*D) →
      ∀ N : ℕ, ∀ ξ : ℝ,
      |ξ|^N*‖profileLaplaceTransform (a03ProfileProduct Φ A) ((ξ:ℂ)*I)‖≤
        a03ProfileProductDerivativeBudget C B N*D := by
  have hK : HasCompactSupport Φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  obtain ⟨C,hC,hCd⟩ := a03_profile_derivative_bounds hK hΦ
  refine ⟨C,hC,?_⟩
  intro A hA B hB D hD hAd N ξ
  exact a03_profile_frequency_dyadic_derivative_bound
    (a03_profile_product_contDiff hΦ (fun x hx => hA x (hs hx)))
    ((a03_profile_product_tsupport Φ A).trans hs) N
    (a03_profile_product_derivative_bound hΦ hs hA hC hB hCd hD hAd N) ξ

end
end Sechstmoment
