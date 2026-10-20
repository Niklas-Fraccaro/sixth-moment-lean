import Sechstmoment.Numerator.U.Separation.Frequency.GammaDualProfile
import Sechstmoment.Numerator.U.Separation.Frequency.SixComposition

namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators ContDiff Topology
noncomputable section
set_option maxHeartbeats 2000000

def a03SixGaussianDualFrequencyKernel (Φ : ℝ → ℂ) (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) (r s : ℝ) (y : A03SixTensorSpace) : ℂ :=
  a03GaussianDualFrequencyProfile Φ T σ α z (-a03RealLogGapSymbol T r s (a03SixGapLinear y))

theorem a03_six_gaussian_dual_frequency_uniform_bounds
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ A R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hA : 0≤A) (hR : 0≤R) :
    ∃ E : ℕ → ℝ, (∀ n, 0≤E n) ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ σ α : MomentShifts, (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤A) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v r s : ℝ, |v|≤θ*Real.log T → 0≤r → r≤1/100 → |s|=1 →
      ContDiffOn ℝ ∞ (a03SixGaussianDualFrequencyKernel Φ T σ α ((c : ℂ)+(v : ℂ)*I) r s)
        a03SixGapDomain ∧ ∀ n : ℕ, ∀ y∈a03SixGapDomain,
      ‖iteratedFDeriv ℝ n (a03SixGaussianDualFrequencyKernel Φ T σ α ((c : ℂ)+(v : ℂ)*I) r s) y‖≤
        E n*T^ε := by
  obtain ⟨C,hC,hdec⟩ := a03_gaussian_dual_frequency_logarithmic_uniform_derivative_bounds
    hΦ hΦs hc hc1 hε hκ hθ hA hR
  refine ⟨a03FrequencySixBudget C, a03FrequencySixBudget_nonneg C hC,?_⟩
  filter_upwards [hdec,Filter.eventually_ge_atTop (0 : ℝ)] with T ht hT
  intro σ α hσ hα hroot v r s hv hr hr1 hs
  have hg := (ht σ α hσ hα hroot v hv).1
  have hd := (ht σ α hσ hα hroot v hv).2
  have hgr : ContDiff ℝ ∞ (fun ξ => a03GaussianDualFrequencyProfile Φ T σ α
      ((c : ℂ)+(v : ℂ)*I) (-ξ)) := hg.comp contDiff_id.neg
  have hdr : ∀ i j ξ, |ξ|^j*‖iteratedDeriv i
      (fun x => a03GaussianDualFrequencyProfile Φ T σ α ((c : ℂ)+(v : ℂ)*I) (-x)) ξ‖≤C i j*T^ε := by
    intro i j ξ
    rw [a03_reflected_frequency_derivative_norm]
    simpa only [abs_neg] using hd i j (-ξ)
  constructor
  · exact (a03_log_frequency_composition_contDiffOn (T := T) hr hr1 hs.le _ hgr).comp_continuousLinearMap
      a03SixGapLinear
  · intro n y hy
    exact a03_six_linear_composition_bound hT hr hr1 hs _ hgr (Real.rpow_nonneg hT _)
      C hC hdr hy n

end
end Sechstmoment
