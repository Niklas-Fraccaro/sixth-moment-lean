import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.Front

/-! Genuine measurability of the physical archimedean factors, including
the values outside the positive-time support. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem a03MeasurableCPow {Ω : Type*} [MeasurableSpace Ω] {f g : Ω→ℂ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (fun x => f x^g x) := by
  simp_rw [Complex.cpow_def]
  apply Measurable.ite (measurableSet_eq_fun hf measurable_const)
  · exact Measurable.ite (measurableSet_eq_fun hg measurable_const) measurable_const measurable_const
  · exact Complex.measurable_exp.comp ((Complex.measurable_log.comp hf).mul hg)

theorem a03VStar_measurable (G : ℂ→ℂ) (hG : Measurable G) :
    Measurable (bblrVStar G) := by
  let z : ℝ×ℝ→ℂ := fun p => (1:ℂ)+(p.2:ℂ)*I
  have hz : Measurable z := by dsimp [z]; fun_prop
  have hx : Measurable (fun p : ℝ×ℝ => (p.1:ℂ)) := by fun_prop
  have hp : Measurable (fun p : ℝ×ℝ => (2*Real.pi:ℂ)^(-2*z p)) :=
    a03MeasurableCPow measurable_const (hz.const_mul (-2))
  have hk : Measurable (fun p : ℝ×ℝ => G (z p)/z p*
      (2*Real.pi:ℂ)^(-2*z p)*(p.1:ℂ)^(-z p)) :=
    (((hG.comp hz).div hz).mul hp).mul (a03MeasurableCPow hx hz.neg)
  unfold bblrVStar verticalIntegral
  exact measurable_const.mul hk.stronglyMeasurable.integral_prod_right'.measurable

theorem a03ZeroModeGCDArchTimeKernel_measurable (Φ : ℝ→ℂ) (hΦ : Measurable Φ)
    (T : ℝ) (σ : MomentShifts) (g a b : ℕ) (s : ℂ) :
    Measurable (fun x => a03ZeroModeGCDArchTimeKernel Φ T σ g a b x s) := by
  have hV := a03VStar_measurable (polarPoleKiller T σ) (polarPoleKiller_differentiable T σ).continuous.measurable
  have harg : Measurable (fun p : ℝ×ℝ => p.1^2/
      ((T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)))^2*p.2^2)) := by fun_prop
  have ht : Measurable (fun p : ℝ×ℝ => (p.2:ℂ)) := by fun_prop
  have hprod : Measurable (fun p : ℝ×ℝ =>
      a03ZeroModeVStarTimeProfile Φ T σ g a b p.1 p.2*(p.2:ℂ)^(-s)) := by
    unfold a03ZeroModeVStarTimeProfile a03ProfileProduct a03ZeroModeVStarTimeAmplitude
    exact ((hΦ.comp measurable_snd).mul (hV.comp harg)).mul (a03MeasurableCPow ht measurable_const)
  unfold a03ZeroModeGCDArchTimeKernel
  have hx : Measurable (fun x : ℝ => (x:ℂ)^s) := a03MeasurableCPow Complex.measurable_ofReal measurable_const
  exact (((hx.mul_const ((T:ℂ)^(-s))).mul_const (Complex.Gamma s)).mul_const (Complex.cos (Real.pi*s/2))).mul
    hprod.stronglyMeasurable.integral_prod_right'.measurable

theorem a03ZeroModeGCDArchKernel_aestronglyMeasurable {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T : ℝ} (hT : 0<T) (σ : MomentShifts) {g a b : ℕ}
    (hg : 0<g) (ha : 0<a) (hb : 0<b) {s : ℂ} (hs : 0<s.re) :
    AEStronglyMeasurable (fun x => a03ZeroModeGCDArchKernel Φ T σ g a b x s)
      (volume.restrict (Ioi 0)) := by
  have hm : AEStronglyMeasurable (fun x => a03ZeroModeGCDArchTimeKernel Φ T σ g a b x s) volume :=
    (a03ZeroModeGCDArchTimeKernel_measurable Φ hΦ.continuous.measurable T σ g a b s).aestronglyMeasurable
  apply hm.restrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (a03ZeroModeGCDArchKernel_eq_time hΦ hSupp hT σ hg ha hb hx hs).symm

end
end Sechstmoment.Source
