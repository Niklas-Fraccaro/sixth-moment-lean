import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Function.LocallyIntegrable


namespace Sechstmoment
open Complex Metric MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

theorem complexIntervalIntegral_hasFDerivAt
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [ProperSpace H]
    (F : H → ℝ → ℂ) (F' : H → ℝ → H →L[ℂ] ℂ)
    (x₀ : H) (r a b : ℝ) (hr : 0 < r) (hab : a ≤ b)
    (hF : ContinuousOn (Function.uncurry F) (closedBall x₀ r ×ˢ Icc a b))
    (hF' : ContinuousOn (Function.uncurry F') (closedBall x₀ r ×ˢ Icc a b))
    (hderiv : ∀ x ∈ closedBall x₀ r, ∀ t ∈ Icc a b,
      HasFDerivAt (fun y => F y t) (F' x t) x) :
    HasFDerivAt (fun x => ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀ := by
  have hslice (x : H) (hx : x ∈ closedBall x₀ r) : ContinuousOn (F x) (Icc a b) :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hx,ht⟩)
  have hslice' (x : H) (hx : x ∈ closedBall x₀ r) : ContinuousOn (F' x) (Icc a b) :=
    hF'.comp (continuous_const.prodMk continuous_id).continuousOn (fun t ht => ⟨hx,ht⟩)
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x₀ r).prod (isCompact_Icc : IsCompact (Icc a b))).exists_bound_of_continuousOn hF'
  have hx₀ : x₀ ∈ closedBall x₀ r := mem_closedBall_self hr.le
  have hmeas : ∀ᶠ x in 𝓝 x₀,
      AEStronglyMeasurable (F x) (volume.restrict (Icc a b)) := by
    filter_upwards [closedBall_mem_nhds x₀ hr] with x hx
    exact (hslice x hx).aestronglyMeasurable measurableSet_Icc
  have hb : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ x ∈ closedBall x₀ r, ‖F' x t‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro x hx
    exact hC (x,t) ⟨hx,ht⟩
  have hd : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ x ∈ closedBall x₀ r,
      HasFDerivAt (fun y => F y t) (F' x t) x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro x hx
    exact hderiv x hx t ht
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (closedBall_mem_nhds x₀ hr) hmeas ((hslice x₀ hx₀).integrableOn_Icc)
    ((hslice' x₀ hx₀).aestronglyMeasurable measurableSet_Icc)
    hb ((continuous_const : Continuous (fun _ : ℝ => C)).integrableOn_Icc) hd
  simpa only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] using h

structure ComplexIntegralFamily
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (U : Set H) (X : Type*) [TopologicalSpace X] where
  value : H → X → ℂ
  derivative : H → X → H →L[ℂ] ℂ
  continuous_value : Continuous (fun p : U × X => value p.1.1 p.2)
  continuous_derivative : Continuous (fun p : U × X => derivative p.1.1 p.2)
  hasFDerivAt : ∀ q ∈ U, ∀ x, HasFDerivAt (fun y => value y x) (derivative q x) q

namespace ComplexIntegralFamily

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [ProperSpace H]
  {U : Set H} {X : Type*} [TopologicalSpace X]

noncomputable def mulAux (F : ComplexIntegralFamily U X) (c : X → ℂ)
    (hc : Continuous c) : ComplexIntegralFamily U X where
  value q x := c x*F.value q x
  derivative q x := c x • F.derivative q x
  continuous_value := (hc.comp continuous_snd).mul F.continuous_value
  continuous_derivative := (hc.comp continuous_snd).smul F.continuous_derivative
  hasFDerivAt q hq x := (F.hasFDerivAt q hq x).const_mul (c x)

noncomputable def reindexAux {Y : Type*} [TopologicalSpace Y]
    (F : ComplexIntegralFamily U X) (g : Y → X) (hg : Continuous g) :
    ComplexIntegralFamily U Y where
  value q y := F.value q (g y)
  derivative q y := F.derivative q (g y)
  continuous_value := F.continuous_value.comp (continuous_fst.prodMk (hg.comp continuous_snd))
  continuous_derivative := F.continuous_derivative.comp
    (continuous_fst.prodMk (hg.comp continuous_snd))
  hasFDerivAt q hq y := F.hasFDerivAt q hq (g y)

noncomputable def mul (F G : ComplexIntegralFamily U X) : ComplexIntegralFamily U X where
  value q x := F.value q x*G.value q x
  derivative q x := F.value q x • G.derivative q x + G.value q x • F.derivative q x
  continuous_value := F.continuous_value.mul G.continuous_value
  continuous_derivative := (F.continuous_value.smul G.continuous_derivative).add
    (G.continuous_value.smul F.continuous_derivative)
  hasFDerivAt q hq x := (F.hasFDerivAt q hq x).mul (G.hasFDerivAt q hq x)

noncomputable def intervalIntegral (F : ComplexIntegralFamily U (X × ℝ))
    (hU : IsOpen U) (a b : ℝ) (hab : a ≤ b) : ComplexIntegralFamily U X where
  value q x := ∫ t in a..b, F.value q (x,t)
  derivative q x := ∫ t in a..b, F.derivative q (x,t)
  continuous_value := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact F.continuous_value.comp (by fun_prop :
      Continuous (fun p : (U × X) × ℝ => (p.1.1,(p.1.2,p.2))))
  continuous_derivative := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact F.continuous_derivative.comp (by fun_prop :
      Continuous (fun p : (U × X) × ℝ => (p.1.1,(p.1.2,p.2))))
  hasFDerivAt := by
    intro q hq x
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hq)
    have hr2 : 0 < r/2 := by linarith
    have hclosed : closedBall q (r/2) ⊆ U :=
      (closedBall_subset_ball (by linarith : r/2 < r)).trans hball
    apply complexIntervalIntegral_hasFDerivAt
      (fun q t => F.value q (x,t)) (fun q t => F.derivative q (x,t))
      q (r/2) a b hr2 hab
    · apply continuousOn_iff_continuous_domRestrict.mpr
      exact F.continuous_value.comp
        ((continuous_subtype_val.fst.subtype_mk (fun p => hclosed p.2.1)).prodMk
          (continuous_const.prodMk continuous_subtype_val.snd))
    · apply continuousOn_iff_continuous_domRestrict.mpr
      exact F.continuous_derivative.comp
        ((continuous_subtype_val.fst.subtype_mk (fun p => hclosed p.2.1)).prodMk
          (continuous_const.prodMk continuous_subtype_val.snd))
    · intro y hy t _
      exact F.hasFDerivAt y (hclosed hy) (x,t)

end ComplexIntegralFamily

end Sechstmoment
