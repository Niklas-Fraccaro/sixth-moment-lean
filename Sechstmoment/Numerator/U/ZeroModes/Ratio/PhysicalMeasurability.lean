import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.Measurability
import Sechstmoment.Numerator.U.ZeroModes.Ratio.PhysicalResidual

/-! Actual product measurability for the physical u/v reconstruction and
its three-contour residual, rather than a measurable-function receipt. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioPhysicalPrefactor_measurable (α : MomentShifts)
    (g a b : ℕ) (A B : ℕ→ℂ) (s : ℂ) :
    Measurable (fun x => a03ZeroModeRatioPhysicalPrefactor α g a b A B x s) := by
  unfold a03ZeroModeRatioPhysicalPrefactor
  exact measurable_const.mul (a03MeasurableCPow Complex.measurable_ofReal measurable_const)

theorem a03ZeroModeRatioPhysicalKernel_measurable_boundary
    {ε c d : ℝ} (hε : 0<ε) (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1≤s.re)
    (hc : a03ZeroModeRatioSecondaryLine ε≤c) (hd : a03ZeroModeRatioSecondaryLine ε≤d)
    (hcd : a03ZeroModeRatioSecondaryLine ε≤c+d) (hc0 : c≠0) (hd0 : d≠0)
    (g : ℕ) (A B : ℕ→ℂ) :
    Measurable (fun p : ℝ×(ℝ×ℝ) => a03ZeroModeRatioPhysicalKernel α g a b A B p.1
      ((c:ℂ)+(p.2.1:ℂ)*I) ((d:ℂ)+(p.2.2:ℂ)*I) s) := by
  let u : ℝ×(ℝ×ℝ)→ℂ := fun p => (c:ℂ)+(p.2.1:ℂ)*I
  let v : ℝ×(ℝ×ℝ)→ℂ := fun p => (d:ℂ)+(p.2.2:ℂ)*I
  have hu : Measurable u := by dsimp [u]; fun_prop
  have hv : Measurable v := by dsimp [v]; fun_prop
  have hx : Measurable (fun p : ℝ×(ℝ×ℝ) => (p.1:ℂ)) := by fun_prop
  have hG : Measurable (fun p => (g:ℂ)^(-1+α 1+α 3-u p-v p-s)) :=
    a03MeasurableCPow measurable_const ((((measurable_const.sub hu).sub hv).sub_const s))
  have hA : Measurable (fun p => (a:ℂ)^(-1+α 1-u p)) :=
    a03MeasurableCPow measurable_const (measurable_const.sub hu)
  have hB : Measurable (fun p => (b:ℂ)^(-1+α 3-v p)) :=
    a03MeasurableCPow measurable_const (measurable_const.sub hv)
  have hX : Measurable (fun p => (p.1:ℂ)^(-α 1-α 3+u p+v p)) :=
    a03MeasurableCPow hx ((measurable_const.add hu).add hv)
  have hK : Measurable (fun p : ℝ×(ℝ×ℝ) => a03ZeroModeRatioArithmeticKernel α a b
      ((c:ℂ)+(p.2.1:ℂ)*I) ((d:ℂ)+(p.2.2:ℂ)*I) s) :=
    (a03ZeroModeRatioArithmeticKernel_continuous_boundary hε α hα ha hb hs
      hc hd hcd hc0 hd0).measurable.comp measurable_snd
  unfold a03ZeroModeRatioPhysicalKernel
  exact ((((measurable_const.mul hG).mul hA).mul hB).mul hX).mul hK

theorem a03ZeroModeRatioPhysicalDoubleIntegral_measurable
    {ε c d : ℝ} (hε : 0<ε) (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {s : ℂ} (hs : 1≤s.re)
    (hc : a03ZeroModeRatioSecondaryLine ε≤c) (hd : a03ZeroModeRatioSecondaryLine ε≤d)
    (hcd : a03ZeroModeRatioSecondaryLine ε≤c+d) (hc0 : c≠0) (hd0 : d≠0)
    (g : ℕ) (A B : ℕ→ℂ) :
    Measurable (fun x => a03ZeroModeRatioDoubleIntegral c d
      (fun u v => a03ZeroModeRatioPhysicalKernel α g a b A B x u v s)) := by
  have hK := a03ZeroModeRatioPhysicalKernel_measurable_boundary hε α hα ha hb hs hc hd hcd hc0 hd0 g A B
  have hr : Measurable (fun p : (ℝ×ℝ)×ℝ => (p.1.1,(p.1.2,p.2))) := by fun_prop
  have hinner := ((hK.comp hr).stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hinnerC : Measurable (fun p : ℝ×ℝ => (1/(2*Real.pi):ℂ)*∫z : ℝ,
      a03ZeroModeRatioPhysicalKernel α g a b A B p.1 ((c:ℂ)+(p.2:ℂ)*I) ((d:ℂ)+(z:ℂ)*I) s) :=
    measurable_const.mul hinner
  have houter := (hinnerC.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  unfold a03ZeroModeRatioDoubleIntegral verticalIntegral
  exact measurable_const.mul houter

theorem a03ZeroModeRatioPhysicalResidual_aestronglyMeasurable
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {s : ℂ} (hs : 1+ε≤s.re) :
    AEStronglyMeasurable (fun x => a03ZeroModeRatioPhysicalResidual ε α g a b A B x s)
      (volume.restrict (Ioi 0)) := by
  have hD := a03ZeroModeRatioPhysicalDoubleIntegral_measurable hε α hα ha.ne' hb.ne'
    (by linarith : 1≤s.re) (c := ε) (d := ε)
    (by unfold a03ZeroModeRatioSecondaryLine; linarith)
    (by unfold a03ZeroModeRatioSecondaryLine; linarith)
    (by unfold a03ZeroModeRatioSecondaryLine; linarith) hε.ne' hε.ne' g A B
  have hM := (a03ZeroModeRatioPhysicalPrefactor_measurable α g a b A B s).mul_const
    (a03ZeroModeRatioArithmeticNumerator α a b 0 0 s)
  apply (hD.sub hM).aestronglyMeasurable.restrict.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have he := a03ZeroModeRatioPhysicalKernel_eq_main_add_residual hε hε1 hδ α hα hρ hg ha hb A B hx hs
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he)

end
end Sechstmoment.Source
