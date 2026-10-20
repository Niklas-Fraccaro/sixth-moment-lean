import Sechstmoment.Numerator.U.ZeroModes.Transforms.SmoothedCosineMellinInversion
import Sechstmoment.Numerator.V.Chi.Gamma


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem chi_cosine_inverse_mellin {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ ⊆ Icc (1:ℝ) 2)
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    verticalIntegral c (fun s : ℂ =>
      (r:ℂ)^(-s)*zetaChi (1-s)*mellin Φ (1-s)) =
      2*a03SmoothedCosine Φ (2*Real.pi*r) := by
  have hp : 0 < 2*Real.pi := by positivity
  have hx : 0 < 2*Real.pi*r := mul_pos hp hr
  rw [a03SmoothedCosine_inverse_Mellin hΦ hSupp hc hx]
  let F : ℝ → ℂ := fun v =>
    let s := (c:ℂ)+(v:ℂ)*I
    (r:ℂ)^(-s)*zetaChi (1-s)*mellin Φ (1-s)
  let G : ℝ → ℂ := fun v =>
    let s := (c:ℂ)+(v:ℂ)*I
    ((2*Real.pi*r:ℝ):ℂ)^(-s)*
      (Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*mellin Φ (1-s))
  have he : F =ᵐ[volume] fun v => 2*G v := by
    filter_upwards [volume.ae_ne (0:ℝ)] with v hv
    let s : ℂ := (c:ℂ)+(v:ℂ)*I
    have hs : s.im ≠ 0 := by simpa [s] using hv
    have hprod : ((2*Real.pi*r:ℝ):ℂ)^(-s) =
        ((2*Real.pi:ℝ):ℂ)^(-s)*(r:ℂ)^(-s) :=
      by simpa only [Complex.ofReal_mul] using
        Complex.mul_cpow_ofReal_nonneg hp.le hr.le (-s)
    change (r:ℂ)^(-s)*zetaChi (1-s)*mellin Φ (1-s) =
      2*(((2*Real.pi*r:ℝ):ℂ)^(-s)*
        (Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*mellin Φ (1-s)))
    rw [chi_one_sub_eq_gamma_cos s hs,hprod]
    ring
  change (1/(2*Real.pi):ℂ)*(∫ v : ℝ, F v) =
    2*((1/(2*Real.pi):ℂ)*(∫ v : ℝ, G v))
  rw [integral_congr_ae he,integral_const_mul]
  ring

end
end Sechstmoment.Source
