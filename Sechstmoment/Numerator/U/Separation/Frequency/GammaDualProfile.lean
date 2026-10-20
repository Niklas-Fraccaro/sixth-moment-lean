import Sechstmoment.Numerator.U.Replacement.TimeGamma.DualDerivatives
import Sechstmoment.Numerator.U.Separation.Frequency.GammaProfile

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def a03GaussianDualTimeProfile (Φ : ℝ → ℂ) (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) : ℝ → ℂ :=
  a03ProfileProduct
    (a03ProfileProduct Φ (fun y => bblrDualMultiplier (T*y) (rawMomentShifts T σ)))
    (bblrGaussianTimeAmplitude T σ α z)

def a03GaussianDualFrequencyProfile (Φ : ℝ → ℂ) (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) (ξ : ℝ) : ℂ :=
  profileLaplaceTransform (a03GaussianDualTimeProfile Φ T σ α z) ((ξ:ℂ)*I)

theorem a03_gaussian_dual_time_profile_tsupport (Φ : ℝ → ℂ) (T : ℝ)
    (σ α : MomentShifts) (z : ℂ) :
    tsupport (a03GaussianDualTimeProfile Φ T σ α z)⊆tsupport Φ :=
  (a03_profile_product_tsupport _ _).trans (a03_profile_product_tsupport _ _)

theorem a03_gaussian_dual_frequency_logarithmic_uniform_derivative_bounds
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ A R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hA : 0≤A) (hR : 0≤R) :
    ∃ C : ℕ → ℕ → ℝ, (∀ k N, 0≤C k N) ∧
      ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤A) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T →
      ContDiff ℝ ∞ (a03GaussianDualFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)) ∧
      ∀ k N : ℕ, ∀ ξ : ℝ,
      |ξ|^N*‖iteratedDeriv k (a03GaussianDualFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)) ξ‖≤
        C k N*T^ε := by
  have hK : HasCompactSupport Φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  have hex (k : ℕ) := a03_profile_derivative_bounds
    (hK.of_isClosed_subset (isClosed_tsupport _) (a03_frequency_weighted_profile_tsupport Φ k))
    (a03_frequency_weighted_profile_contDiff hΦ k)
  choose C₀ hC₀ hC₀d using hex
  obtain ⟨B,hB,hBd⟩ := bblrGaussianTimeAmplitude_logarithmic_uniform_subpower_bounds
    hc hc1 hε hκ hθ hA
  obtain ⟨E,hE,hEd⟩ := bblrDualMultiplier_normalizedTime_uniform_derivative_bounds hR
  let P : ℕ → ℕ → ℝ := fun k j => a03ProfileProductDerivativeBudget (C₀ k) E j
  have hP (k j : ℕ) : 0≤P k j := a03_profile_product_budget_nonneg (hC₀ k) hE j
  refine ⟨fun k N => a03ProfileProductDerivativeBudget (P k) B N,
    fun k N => a03_profile_product_budget_nonneg (hP k) hB N,?_⟩
  filter_upwards [hBd,hEd,bblrGamma_logarithmic_strip_large hc.le hc1 hθ,
    eventually_ge_atTop (8*(A+1)),eventually_ge_atTop (192*(R+R^2)+8),
    eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hg hd hlarge hAT hRT hT hlog
  intro σ α hσ hα hroot v hv
  let D : ℝ → ℂ := fun y => bblrDualMultiplier (T*y) (rawMomentShifts T σ)
  let G : ℝ → ℂ := bblrGaussianTimeAmplitude T σ α ((c:ℂ)+(v:ℂ)*I)
  have hDc (x : ℝ) (hx : x∈Icc (1:ℝ) 2) : ContDiffAt ℝ ∞ D x :=
    (bblrDualMultiplier_normalizedTime_contDiffAt hR hlog hRT σ hσ hx).of_le (by simp)
  have hGc (x : ℝ) (hx : x∈Icc (1:ℝ) 2) : ContDiffAt ℝ ∞ G x :=
    (bblrGaussianTimeAmplitude_contDiffAt hA hAT σ α hα (hlarge v hv) hx).of_le (by simp)
  have hDder (j : ℕ) (x : ℝ) (hx : x∈Icc (1:ℝ) 2) : ‖iteratedDeriv j D x‖≤E j*1 := by
    simpa only [mul_one] using hd σ hσ x hx j
  have hGder (j : ℕ) (x : ℝ) (hx : x∈Icc (1:ℝ) 2) : ‖iteratedDeriv j G x‖≤B j*T^ε :=
    hg σ α hα hroot v hv x hx j
  have hPD : ContDiff ℝ ∞ (a03ProfileProduct Φ D) :=
    a03_profile_product_contDiff hΦ (fun x hx => hDc x (hs hx))
  have hPDs : tsupport (a03ProfileProduct Φ D)⊆Icc 1 2 :=
    (a03_profile_product_tsupport Φ D).trans hs
  have hPG : ContDiff ℝ ∞ (a03GaussianDualTimeProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)) :=
    a03_profile_product_contDiff hPD (fun x hx => hGc x (hPDs hx))
  have hPGs : tsupport (a03GaussianDualTimeProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I))⊆Icc 1 2 :=
    (a03_gaussian_dual_time_profile_tsupport Φ T σ α _).trans hs
  have hPGk : HasCompactSupport (a03GaussianDualTimeProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hPGs
  refine ⟨?_,?_⟩
  · have he : ContDiff ℂ ∞
        (profileLaplaceTransform (a03GaussianDualTimeProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I))) :=
      (profileLaplaceTransform_entire hPGk hPG.continuous).contDiff
    exact (he.restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
  · intro k N ξ
    unfold a03GaussianDualFrequencyProfile
    rw [a03_profile_frequency_derivative_formula hPGk hPG k]
    have he : a03FrequencyWeightedProfile
        (a03GaussianDualTimeProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)) k=
        a03ProfileProduct (a03ProfileProduct (a03FrequencyWeightedProfile Φ k) D) G := by
      funext x
      dsimp [a03FrequencyWeightedProfile,a03GaussianDualTimeProfile,a03ProfileProduct,D,G]
      ring
    rw [he]
    have hW : ContDiff ℝ ∞ (a03FrequencyWeightedProfile Φ k) :=
      a03_frequency_weighted_profile_contDiff hΦ k
    have hWs : tsupport (a03FrequencyWeightedProfile Φ k)⊆Icc 1 2 :=
      (a03_frequency_weighted_profile_tsupport Φ k).trans hs
    have hWD : ContDiff ℝ ∞ (a03ProfileProduct (a03FrequencyWeightedProfile Φ k) D) :=
      a03_profile_product_contDiff hW (fun x hx => hDc x (hWs hx))
    have hWDs : tsupport (a03ProfileProduct (a03FrequencyWeightedProfile Φ k) D)⊆Icc 1 2 :=
      (a03_profile_product_tsupport _ _).trans hWs
    have hWDd (j : ℕ) (x : ℝ) :
        ‖iteratedDeriv j (a03ProfileProduct (a03FrequencyWeightedProfile Φ k) D) x‖≤P k j := by
      simpa only [mul_one] using a03_profile_product_derivative_bound
        hW hWs hDc (hC₀ k) hE (hC₀d k) (by norm_num : (0:ℝ)≤1) hDder j x
    exact a03_profile_frequency_dyadic_derivative_bound
      (a03_profile_product_contDiff hWD (fun x hx => hGc x (hWDs hx)))
      ((a03_profile_product_tsupport _ _).trans hWDs) N
      (a03_profile_product_derivative_bound hWD hWDs hGc (hP k) hB hWDd
        (Real.rpow_nonneg hT.le _) hGder N) ξ

end
end Sechstmoment
