import Sechstmoment.Analysis.Calculus.CompactProduct
import Sechstmoment.Analysis.Complex.PositivePowerBounds
import Sechstmoment.Numerator.V.Chi.LogBandProfile


namespace Sechstmoment.Source
open Complex Real Set
open scoped ContDiff BigOperators
noncomputable section

def noDPLogBandMask : ℝ → ℂ :=
  a03ProfileProduct noDPPositiveBandWindow
    (fun u => (noDPFrequencyBump (-50*Real.log u):ℂ))

theorem noDPLogBandMask_tsupport : tsupport noDPLogBandMask ⊆ Icc (3/4:ℝ) (5/4) :=
  (a03_profile_product_tsupport _ _).trans noDPPositiveBandWindow_tsupport

theorem noDPLogBandMask_contDiff : ContDiff ℝ ∞ noDPLogBandMask := by
  apply a03_profile_product_contDiff noDPPositiveBandWindow_contDiff
  intro u hu
  have hu0 : 0 < u := by linarith [(noDPPositiveBandWindow_tsupport hu).1]
  exact Complex.ofRealCLM.contDiff.contDiffAt.comp u
    (noDPFrequencyBump.contDiff.contDiffAt.comp u
      (contDiffAt_const.mul (Real.contDiffAt_log.mpr hu0.ne')))

def noDPLogBandAmplitude (c : ℝ) : ℝ → ℂ :=
  a03ProfileProduct noDPLogBandMask (fun u => (u:ℂ)^((c-1:ℝ):ℂ))

theorem noDPLogBandAmplitude_tsupport (c : ℝ) :
    tsupport (noDPLogBandAmplitude c) ⊆ Icc (3/4:ℝ) (5/4) :=
  (a03_profile_product_tsupport _ _).trans noDPLogBandMask_tsupport

theorem noDPLogBandAmplitude_contDiff (c : ℝ) : ContDiff ℝ ∞ (noDPLogBandAmplitude c) := by
  apply a03_profile_product_contDiff noDPLogBandMask_contDiff
  intro u hu
  have hu0 : 0 < u := by linarith [(noDPLogBandMask_tsupport hu).1]
  exact positive_cpow_contDiffAt ((c-1:ℝ):ℂ) hu0

theorem noDPLogBandAmplitude_uniform_derivatives :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ c ∈ Icc (1:ℝ) 2, ∀ n u,
      ‖iteratedDeriv n (noDPLogBandAmplitude c) u‖ ≤ C n := by
  have hK : HasCompactSupport noDPLogBandMask :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) noDPLogBandMask_tsupport
  obtain ⟨D,hD,hd⟩ := a03_profile_derivative_bounds hK noDPLogBandMask_contDiff
  let B : ℕ → ℝ := fun j => 2*((4:ℝ)*((j:ℝ)+1))^j
  have hB (j : ℕ) : 0 ≤ B j := by dsimp only [B]; positivity
  let C : ℕ → ℝ := fun n => a03ProfileProductDerivativeBudget D B n
  have hC (n : ℕ) : 0 ≤ C n := by
    dsimp only [C,a03ProfileProductDerivativeBudget]
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hD i)) (hB _))
  refine ⟨C,hC,?_⟩
  intro c hc n u
  have hs : tsupport noDPLogBandMask ⊆ Icc (1/2:ℝ) 2 := by
    intro x hx
    have H := noDPLogBandMask_tsupport hx
    constructor <;> linarith [H.1,H.2]
  have hA (x : ℝ) (hx : x ∈ Icc (1/2:ℝ) 2) :
      ContDiffAt ℝ ∞ (fun y : ℝ => (y:ℂ)^((c-1:ℝ):ℂ)) x :=
    positive_cpow_contDiffAt _ (by linarith [hx.1])
  have hAd (j : ℕ) (_hj : j ≤ n) (x : ℝ) (hx : x ∈ Icc (1/2:ℝ) 2) :
      ‖iteratedDeriv j (fun y : ℝ => (y:ℂ)^((c-1:ℝ):ℂ)) x‖ ≤ B j*(1:ℝ)^j := by
    simpa only [B,one_pow,mul_one] using positive_unit_power_derivative_bound j
      (c := c-1) ⟨by linarith [hc.1],by linarith [hc.2]⟩ hx
  have H := compact_derivative_product_bound noDPLogBandMask_contDiff
    (T := 1) (by norm_num) hs hA hD hB hd n hAd u
  simpa only [C,noDPLogBandAmplitude,one_pow,mul_one] using! H

theorem noDPLogBandProfile_eq_amplitude (h : SchwartzMap ℝ ℂ) (T c u : ℝ) :
    noDPLogBandProfile h T c u =
      ((T/(2*Real.pi):ℝ):ℂ)*noDPLogBandAmplitude c u*h (-T*Real.log u/(2*Real.pi)) := by
  unfold noDPLogBandProfile noDPLogBandAmplitude noDPLogBandMask a03ProfileProduct
  ring

end
end Sechstmoment.Source
