import SixthMoment.Numerator.U.ZeroModes.GlobalMeasurability
import SixthMoment.Numerator.U.ZeroModes.Ratio.PhysicalResidual

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioResidual_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (ε : ℝ) (α : MomentShifts) {a b : ℕ} (ha : a≠0) (hb : b≠0)
    {L M : Ω→ℝ} {S : Ω→ℂ} (hL : Measurable L) (hM : Measurable M) (hS : Measurable S) :
    Measurable (fun x => a03ZeroModeRatioResidual (L x) (M x) ε α a b (S x)) := by
  let p := a03ZeroModeRatioPrimaryLine ε
  let q := a03ZeroModeRatioSecondaryLine ε
  have hU : Measurable (fun x : (Ω×ℝ)×ℝ => (p:ℂ)+(x.1.2:ℂ)*I) := by fun_prop
  have hV : Measurable (fun x : (Ω×ℝ)×ℝ => (p:ℂ)+(x.2:ℂ)*I) := by fun_prop
  have hSt : Measurable (fun x : (Ω×ℝ)×ℝ => S x.1.1) :=
    (hS.comp measurable_fst).comp measurable_fst
  have hLt : Measurable (fun x : (Ω×ℝ)×ℝ => (L x.1.1:ℂ)) :=
    Complex.measurable_ofReal.comp ((hL.comp measurable_fst).comp measurable_fst)
  have hMt : Measurable (fun x : (Ω×ℝ)×ℝ => (M x.1.1:ℂ)) :=
    Complex.measurable_ofReal.comp ((hM.comp measurable_fst).comp measurable_fst)
  have hK : Measurable (fun x : (Ω×ℝ)×ℝ => a03ZeroModeRatioWeightedKernel (L x.1.1) (M x.1.1)
      α a b ((p:ℂ)+(x.1.2:ℂ)*I) ((p:ℂ)+(x.2:ℂ)*I) (S x.1.1)) :=
    (Complex.measurable_exp.comp ((hLt.mul hU).add (hMt.mul hV))).mul
      (a03ZeroModeRatioArithmeticKernel_measurable_comp α ha hb hU hV hSt)
  have hinner : Measurable (fun x : Ω×ℝ => (1/(2*Real.pi):ℂ)*∫z : ℝ,
      a03ZeroModeRatioWeightedKernel (L x.1) (M x.1) α a b ((p:ℂ)+(x.2:ℂ)*I)
        ((p:ℂ)+(z:ℂ)*I) (S x.1)) :=
    measurable_const.mul (hK.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hD : Measurable (fun x => a03ZeroModeRatioDoubleIntegral p p
      (fun u v => a03ZeroModeRatioWeightedKernel (L x) (M x) α a b u v (S x))) := by
    unfold a03ZeroModeRatioDoubleIntegral verticalIntegral
    exact measurable_const.mul (hinner.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have hZ : Measurable (fun x : Ω×ℝ => (q:ℂ)+(x.2:ℂ)*I) := by fun_prop
  have hS2 : Measurable (fun x : Ω×ℝ => S x.1) := hS.comp measurable_fst
  have hL2 : Measurable (fun x : Ω×ℝ => (L x.1:ℂ)) := Complex.measurable_ofReal.comp (hL.comp measurable_fst)
  have hM2 : Measurable (fun x : Ω×ℝ => (M x.1:ℂ)) := Complex.measurable_ofReal.comp (hM.comp measurable_fst)
  have hleft : Measurable (fun x : Ω×ℝ => a03ZeroModeRatioWeightedLeftResidue (L x.1) (M x.1)
      α a b (S x.1) ((q:ℂ)+(x.2:ℂ)*I)) :=
    (Complex.measurable_exp.comp (hM2.mul hZ)).mul
      ((a03ZeroModeRatioArithmeticNumerator_measurable_comp α ha hb measurable_const hZ hS2).div hZ)
  have hright : Measurable (fun x : Ω×ℝ => a03ZeroModeRatioWeightedRightResidue (L x.1) (M x.1)
      α a b (S x.1) ((q:ℂ)+(x.2:ℂ)*I)) :=
    (Complex.measurable_exp.comp (hL2.mul hZ)).mul
      ((a03ZeroModeRatioArithmeticNumerator_measurable_comp α ha hb hZ measurable_const hS2).div hZ)
  unfold a03ZeroModeRatioResidual verticalIntegral
  exact (hD.add (measurable_const.mul (hleft.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable)).add
    (measurable_const.mul (hright.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable)

theorem a03ZeroModeRatioPhysicalResidual_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (ε : ℝ) (α : MomentShifts) (g : ℕ) {a b : ℕ} (ha : a≠0) (hb : b≠0)
    (A B : ℕ→ℂ) {X : Ω→ℝ} {S : Ω→ℂ} (hX : Measurable X) (hS : Measurable S) :
    Measurable (fun x => a03ZeroModeRatioPhysicalResidual ε α g a b A B (X x) (S x)) := by
  have hG : Measurable (fun x => (g:ℂ)^(-1+α 1+α 3-S x)) :=
    a03MeasurableCPow measurable_const (measurable_const.sub hS)
  have hXp : Measurable (fun x => (X x:ℂ)^(-α 1-α 3)) :=
    a03MeasurableCPow (Complex.measurable_ofReal.comp hX) measurable_const
  have hP : Measurable (fun x => a03ZeroModeRatioPhysicalPrefactor α g a b A B (X x) (S x)) :=
    (((measurable_const.mul hG).mul_const ((a:ℂ)^(-1+α 1))).mul_const ((b:ℂ)^(-1+α 3))).mul hXp
  have hL : Measurable (fun x => a03ZeroModeRatioPhysicalLogLeft g a (X x)) :=
    Real.measurable_log.comp (hX.div_const (g*a:ℕ))
  have hM : Measurable (fun x => a03ZeroModeRatioPhysicalLogRight g b (X x)) :=
    Real.measurable_log.comp (hX.div_const (g*b:ℕ))
  exact hP.mul (a03ZeroModeRatioResidual_measurable_comp ε α ha hb hL hM hS)

theorem a03ZeroModeGCDArchTimeKernel_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (Φ : ℝ→ℂ) (hΦ : Measurable Φ) (T : ℝ) (σ : MomentShifts) (g a b : ℕ)
    {X : Ω→ℝ} {S : Ω→ℂ} (hX : Measurable X) (hS : Measurable S) :
    Measurable (fun x => a03ZeroModeGCDArchTimeKernel Φ T σ g a b (X x) (S x)) := by
  have hV := a03VStar_measurable (polarPoleKiller T σ) (polarPoleKiller_differentiable T σ).continuous.measurable
  have harg : Measurable (fun p : Ω×ℝ => (X p.1)^2/
      ((T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)))^2*p.2^2)) :=
    (hX.comp measurable_fst |>.pow_const 2).div (measurable_const.mul (measurable_snd.pow_const 2))
  have ht : Measurable (fun p : Ω×ℝ => (p.2:ℂ)) := by fun_prop
  have hS2 : Measurable (fun p : Ω×ℝ => S p.1) := hS.comp measurable_fst
  have hprod : Measurable (fun p : Ω×ℝ =>
      a03ZeroModeVStarTimeProfile Φ T σ g a b (X p.1) p.2*(p.2:ℂ)^(-S p.1)) :=
    ((hΦ.comp measurable_snd).mul (hV.comp harg)).mul (a03MeasurableCPow ht hS2.neg)
  unfold a03ZeroModeGCDArchTimeKernel
  exact ((((a03MeasurableCPow (Complex.measurable_ofReal.comp hX) hS).mul
    (a03MeasurableCPow measurable_const hS.neg)).mul (a03Gamma_measurable.comp hS)).mul
      (Complex.measurable_cos.comp ((hS.const_mul Real.pi).div_const 2))).mul
        (hprod.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

end
end SixthMoment.Source
