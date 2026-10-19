import Sechstmoment.Analysis.Mellin.VerticalIntegral
import Sechstmoment.Arithmetic.QuadraticDivisor.Definitions
import Sechstmoment.Numerator.U.ZeroModes.Transforms.GammaCosPolynomial
import Sechstmoment.Numerator.U.ZeroModes.Transforms.SmoothedCosineMellinInversionBase

/-! Genuine complete inverse Mellin formula for the actual time-smoothed
cosine, on every positive real line. All vertical convergence follows
from the proved complex-Laplace Gamma bound and actual profile decay. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem a03SmoothedCosine_vertical_integrable {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c : ℝ} (hc : 0<c) : VerticalIntegrable (mellin (a03SmoothedCosine Φ)) c := by
  obtain ⟨N,C,hC,hΓ⟩ := a03GammaCos_vertical_polynomial_bound c hc
  exact a03SmoothedCosine_vertical_integrable_of_GammaCos_bound hΦ hSupp hc hC N hΓ

theorem a03SmoothedCosine_mellinInv_mellin {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c x : ℝ} (hc : 0<c) (hx : 0<x) :
    mellinInv c (mellin (a03SmoothedCosine Φ)) x=a03SmoothedCosine Φ x := by
  have hK : HasCompactSupport Φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hSupp
  exact mellinInv_mellin_eq c _ hx
    (a03SmoothedCosine_hasMellin_gamma hΦ hSupp (s:=(c:ℂ)) (by simpa using hc)).1
    (a03SmoothedCosine_vertical_integrable hΦ hSupp hc)
    (a03SmoothedCosine_continuous hΦ.continuous hK).continuousAt

theorem a03SmoothedCosine_inverse_Mellin {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c x : ℝ} (hc : 0<c) (hx : 0<x) :
    a03SmoothedCosine Φ x=verticalIntegral c (fun s : ℂ =>
      (x:ℂ)^(-s)*(Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*mellin Φ (1-s))) := by
  rw [←a03SmoothedCosine_mellinInv_mellin hΦ hSupp hc hx]
  unfold mellinInv verticalIntegral
  simp only [Complex.real_smul,smul_eq_mul]
  push_cast
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro v
  dsimp only
  rw [a03SmoothedCosine_mellin_eq_gamma_mellin hΦ hSupp (by simpa using hc)]

end
end Sechstmoment
