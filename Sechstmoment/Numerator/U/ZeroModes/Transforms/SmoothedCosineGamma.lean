import Sechstmoment.Numerator.U.ZeroModes.Transforms.CosineGammaLimit
import Sechstmoment.Numerator.U.ZeroModes.Transforms.DampedCosineFubini

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem a03SmoothedCosine_mellin_eq_gamma {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {s : ℂ} (hs : 0<s.re) :
    mellin (a03SmoothedCosine Φ) s=
      Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*
        ∫ t : ℝ,Φ t*(t:ℂ)^(-s) := by
  have hK : HasCompactSupport Φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hSupp
  have hzero : ∀ t : ℝ,t∉Icc (1:ℝ) 2 → Φ t=0 := by
    intro t ht
    exact Function.notMem_support.mp (fun hm => ht (hSupp (subset_tsupport _ hm)))
  have hleft := a03SmoothedCosine_abel_mellin_tendsto hK hΦ hs
  have hright := a03CosineGamma_time_integral_tendsto s hΦ.continuous hK hzero
  apply tendsto_nhds_unique hleft
  convert hright using 1
  funext n
  rw [a03DampedSmoothedCosine_mellin_eq_gamma hΦ.continuous hK hs n]
  congr 1
  funext t
  unfold a03CosineGammaKernel
  ring

theorem a03SmoothedCosine_hasMellin_gamma {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {s : ℂ} (hs : 0<s.re) :
    HasMellin (a03SmoothedCosine Φ) s
      (Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*∫ t : ℝ,Φ t*(t:ℂ)^(-s)) :=
  ⟨a03SmoothedCosine_mellinConvergent
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hSupp) hΦ hs,
    a03SmoothedCosine_mellin_eq_gamma hΦ hSupp hs⟩


theorem a03SmoothedCosine_scaled_hasMellin_gamma {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {s : ℂ} (hs : 0<s.re) {T : ℝ} (hT : 0<T) :
    HasMellin (fun u : ℝ => a03SmoothedCosine Φ (T*u)) s
      ((T:ℂ)^(-s)*(Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*
        ∫ t : ℝ,Φ t*(t:ℂ)^(-s))) := by
  refine ⟨(MellinConvergent.comp_mul_left hT).mpr
    (a03SmoothedCosine_hasMellin_gamma hΦ hSupp hs).1,?_⟩
  rw [mellin_comp_mul_left _ s hT,a03SmoothedCosine_mellin_eq_gamma hΦ hSupp hs]
  rfl

end
end Sechstmoment
