import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.Front
import Sechstmoment.Numerator.U.ZeroModes.Transforms.CosineGapMellinSeries

/-! The genuine native gap sum, including its actual x/T scaling,
is the Archimedean Mellin factor times the zeta Dirichlet series. -/
namespace Sechstmoment.Source
open Complex Real Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem a03NativeGap_inversePower_factor {T d x : ℝ} (hT : 0<T) (hd : 0<d)
    (hx : 0<x) (s : ℂ) :
    ((T*d/x:ℝ):ℂ)^(-s)=(d:ℂ)^(-s)*(x:ℂ)^s*(T:ℂ)^(-s) := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (mul_pos hT hd).le hx.le,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hT.le hd.le,Complex.cpow_neg (x:ℂ)]
  simp only [div_inv_eq_mul]
  ring

theorem a03ZeroModeNativeGap_norm_summable {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T : ℝ} (hT : 0<T) (σ : MomentShifts) {g a b d : ℕ}
    (hg : 0<g) (ha : 0<a) (hb : 0<b) (hd : 0<d)
    {x : ℝ} (hx : 0<x) {cs : ℝ} (hcs : 1<cs) :
    Summable (fun h : ℕ => ‖a03SmoothedCosine
      (a03ZeroModeVStarTimeProfile Φ T σ g a b x) (T*(d:ℝ)*((h:ℝ)+1)/x)‖) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hF := a03ZeroModeVStarTimeProfile_contDiff hΦ hSupp hT σ hg ha hb hx
  have hFs := (a03ZeroModeVStarTimeProfile_support Φ T σ g a b x).trans hSupp
  convert a03SmoothedCosine_gap_norm_summable hF hFs hcs
    (div_pos (mul_pos hT hdR) hx) using 1
  funext h
  congr 2
  ring

theorem a03ZeroModeNativeGap_sum_eq_arch_Mellin {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T : ℝ} (hT : 0<T) (σ : MomentShifts) {g a b d : ℕ}
    (hg : 0<g) (ha : 0<a) (hb : 0<b) (hd : 0<d)
    {x : ℝ} (hx : 0<x) {cs : ℝ} (hcs : 1<cs) :
    (∑' h : ℕ,a03SmoothedCosine (a03ZeroModeVStarTimeProfile Φ T σ g a b x)
      (T*(d:ℝ)*((h:ℝ)+1)/x))=
      verticalIntegral cs (fun s : ℂ => (d:ℂ)^(-s)*riemannZeta s*
        a03ZeroModeGCDArchKernel Φ T σ g a b x s) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hF := a03ZeroModeVStarTimeProfile_contDiff hΦ hSupp hT σ hg ha hb hx
  have hFs := (a03ZeroModeVStarTimeProfile_support Φ T σ g a b x).trans hSupp
  have he (h : ℕ) : T*(d:ℝ)*((h:ℝ)+1)/x=(T*(d:ℝ)/x)*((h:ℝ)+1) := by ring
  simp_rw [he]
  rw [a03SmoothedCosine_gap_sum_inverse_Mellin hF hFs hcs (div_pos (mul_pos hT hdR) hx)]
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro v
  dsimp only
  rw [a03NativeGap_inversePower_factor hT hdR hx,
    a03ZeroModeGCDArchKernel_eq_time hΦ hSupp hT σ hg ha hb hx
      (by simpa using (zero_lt_one.trans hcs))]
  unfold a03ZeroModeGCDArchTimeKernel
  rw [a03PositiveTime_inversePowerIntegral_eq_mellin hFs]
  push_cast
  ring

end
end Sechstmoment.Source
