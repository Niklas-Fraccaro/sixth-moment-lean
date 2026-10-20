import SixthMoment.Numerator.U.Replacement.TimeGamma.LogStrip
import SixthMoment.Numerator.U.Separation.Frequency.FourierDerivatives

namespace SixthMoment
open Complex Real Source MeasureTheory Set
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def a03GaussianTimeProfile (Φ : ℝ → ℂ) (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) : ℝ → ℂ :=
  a03ProfileProduct Φ (bblrGaussianTimeAmplitude T σ α z)

def a03GaussianFrequencyProfile (Φ : ℝ → ℂ) (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) (ξ : ℝ) : ℂ :=
  profileLaplaceTransform (a03GaussianTimeProfile Φ T σ α z) ((ξ:ℂ)*I)

theorem a03_profile_product_budget_nonneg {C B : ℕ → ℝ}
    (hC : ∀ n, 0≤C n) (hB : ∀ n, 0≤B n) (N : ℕ) :
    0≤a03ProfileProductDerivativeBudget C B N := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hB (N-i))

theorem a03_gaussian_time_profile_contDiff {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {T A : ℝ} (hA : 0≤A) (hAT : 8*(A+1)≤T) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤A) {z : ℂ} (hlarge : 192*(‖z‖+‖z‖^2)<T) :
    ContDiff ℝ ∞ (a03GaussianTimeProfile Φ T σ α z) := by
  apply a03_profile_product_contDiff hΦ
  intro x hx
  exact (bblrGaussianTimeAmplitude_contDiffAt hA hAT σ α hα hlarge (hs hx)).of_le (by simp)

theorem a03_gaussian_time_profile_tsupport (Φ : ℝ → ℂ) (T : ℝ)
    (σ α : MomentShifts) (z : ℂ) :
    tsupport (a03GaussianTimeProfile Φ T σ α z)⊆tsupport Φ :=
  a03_profile_product_tsupport _ _

theorem a03_gaussian_frequency_uniform_derivative_bounds
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ) :
    ∃ C : ℕ → ℕ → ℝ, (∀ k N, 0≤C k N) ∧
      ∀ (T A : ℝ) (σ α : MomentShifts) (v : ℝ),
      1<T → 1≤Real.log T → 0≤A → 8*(A+1)≤T →
      (∀ j, ‖α j‖≤A) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      192*(‖(c:ℂ)+(v:ℂ)*I‖+‖(c:ℂ)+(v:ℂ)*I‖^2)<T →
      ∀ k N : ℕ, ∀ ξ : ℝ,
      |ξ|^N*‖iteratedDeriv k (a03GaussianFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)) ξ‖≤
        C k N*T^ε := by
  obtain ⟨B,hB,hBd⟩ := bblrGaussianTimeAmplitude_uniform_subpower_derivatives hc hc1 hε hκ
  obtain ⟨C,hC,hCd⟩ := a03_profile_product_all_frequency_derivatives hΦ hs
  refine ⟨fun k N => a03ProfileProductDerivativeBudget (C k) B N,
    fun k N => a03_profile_product_budget_nonneg (hC k) hB N,?_⟩
  intro T A σ α v hT hlog hA hAT hα hroot hlarge k N ξ
  have hAc (x : ℝ) (hx : x∈Icc (1:ℝ) 2) :
      ContDiffAt ℝ ∞ (bblrGaussianTimeAmplitude T σ α ((c:ℂ)+(v:ℂ)*I)) x :=
    (bblrGaussianTimeAmplitude_contDiffAt hA hAT σ α hα hlarge hx).of_le (by simp)
  have hAd (j : ℕ) (x : ℝ) (hx : x∈Icc (1:ℝ) 2) :
      ‖iteratedDeriv j (bblrGaussianTimeAmplitude T σ α ((c:ℂ)+(v:ℂ)*I)) x‖≤B j*T^ε :=
    hBd T A σ α v x hT hlog hA hAT hα hroot hlarge hx j
  exact hCd _ hAc B hB (T^ε) (Real.rpow_nonneg (by linarith) _) hAd k N ξ

theorem a03_gaussian_frequency_profile_contDiff {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {T A : ℝ} (hA : 0≤A) (hAT : 8*(A+1)≤T) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤A) {z : ℂ} (hlarge : 192*(‖z‖+‖z‖^2)<T) :
    ContDiff ℝ ∞ (a03GaussianFrequencyProfile Φ T σ α z) := by
  have hc := a03_gaussian_time_profile_contDiff hΦ hs hA hAT σ α hα hlarge
  have hK : HasCompactSupport (a03GaussianTimeProfile Φ T σ α z) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      ((a03_gaussian_time_profile_tsupport Φ T σ α z).trans hs)
  have he : ContDiff ℂ ∞ (profileLaplaceTransform (a03GaussianTimeProfile Φ T σ α z)) :=
    (profileLaplaceTransform_entire hK hc.continuous).contDiff
  exact (he.restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.mul contDiff_const)

theorem a03_gaussian_frequency_logarithmic_uniform_derivative_bounds
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ A : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hA : 0≤A) :
    ∃ C : ℕ → ℕ → ℝ, (∀ k N, 0≤C k N) ∧
      ∀ᶠ T : ℝ in Filter.atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖≤A) → (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T →
      ContDiff ℝ ∞ (a03GaussianFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)) ∧
      ∀ k N : ℕ, ∀ ξ : ℝ,
      |ξ|^N*‖iteratedDeriv k (a03GaussianFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)) ξ‖≤
        C k N*T^ε := by
  obtain ⟨C,hC,hCd⟩ := a03_gaussian_frequency_uniform_derivative_bounds hΦ hs hc hc1 hε hκ
  refine ⟨C,hC,?_⟩
  filter_upwards [bblrGamma_logarithmic_strip_large hc.le hc1 hθ,
    Filter.eventually_gt_atTop (1:ℝ),Filter.eventually_ge_atTop (8*(A+1)),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))]
    with T hlarge hT hAT hlog
  intro σ α hα hroot v hv
  refine ⟨a03_gaussian_frequency_profile_contDiff hΦ hs hA hAT σ α hα (hlarge v hv),?_⟩
  exact hCd T A σ α v hT hlog hA hAT hα hroot (hlarge v hv)

end
end SixthMoment
