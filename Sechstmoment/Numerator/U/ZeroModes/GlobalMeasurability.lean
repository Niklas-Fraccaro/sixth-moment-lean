import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.Measurability

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem a03RiemannZeta_measurable : Measurable riemannZeta :=
  measurable_of_continuousOn_compl_singleton 1 differentiableOn_riemannZeta.continuousOn

theorem a03Gamma_measurable : Measurable Complex.Gamma := by
  have hc : ContinuousOn Complex.Gamma (Set.range (fun n : ℕ => -(n:ℂ)))ᶜ := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z _).continuousAt.continuousWithinAt
    intro n he
    exact hz ⟨n,he.symm⟩
  apply hc.measurable_of_countable_compl
  simpa only [compl_compl] using countable_range (fun n : ℕ => -(n:ℂ))

theorem a03EtaCorrection_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (p : ℕ) {X Y Z : Ω→ℂ} (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    Measurable (fun x => bblrEtaCorrection p (X x) (Y x) (Z x)) := by
  unfold bblrEtaCorrection
  exact ((a03MeasurableCPow measurable_const (hX.const_add 1).neg).const_sub 1 |>.mul
    ((a03MeasurableCPow measurable_const (hY.const_add 1).neg).const_sub 1)).div
      ((a03MeasurableCPow measurable_const (hZ.const_add 2).neg).const_sub 1)

theorem a03EtaArithmetic_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (α β γ δ : ℂ) {a : ℕ} (ha : a≠0) {U V S : Ω→ℂ}
    (hU : Measurable U) (hV : Measurable V) (hS : Measurable S) :
    Measurable (fun x => bblrEtaArithmetic α β γ δ (U x) (V x) (S x) a) := by
  simp_rw [bblrEtaArithmetic_apply _ _ _ _ _ _ _ ha]
  apply Finset.measurable_sum
  intro l _
  apply Measurable.mul
  · exact a03MeasurableCPow measurable_const (((hV.const_mul 2).const_add (γ-δ)).add hS).neg
  · apply Finset.measurable_prod
    intro p _
    exact a03EtaCorrection_measurable_comp p
      (((hU.const_mul 2).const_add (α-β+γ-δ)).add (hV.const_mul 2) |>.add hS)
      ((hV.const_mul 2).const_add (γ-δ))
      (((hU.const_mul 2).const_add (α-β+γ-δ)).add (hV.const_mul 2))

theorem a03ZeroModeRatioArithmeticNumerator_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (α : MomentShifts) {a b : ℕ} (ha : a≠0) (hb : b≠0) {U V S : Ω→ℂ}
    (hU : Measurable U) (hV : Measurable V) (hS : Measurable S) :
    Measurable (fun x => a03ZeroModeRatioArithmeticNumerator α a b (U x) (V x) (S x)) := by
  have hE : Measurable (fun x => a03ZeroModeRatioEulerArgument α (U x) (V x)) :=
    ((hU.const_mul 2).const_add (2+α 0-α 1+α 2-α 3)).add (hV.const_mul 2)
  unfold a03ZeroModeRatioArithmeticNumerator a03ZeroModeRatioRemovedPair a03ZeroModeRatioEtaPair
  exact (((((a03ZeroModeRatioRemovedDifference_differentiable α 0).continuous.measurable.comp hU).mul
    ((a03ZeroModeRatioRemovedDifference_differentiable α 1).continuous.measurable.comp hV)).mul
      (a03RiemannZeta_measurable.comp hS)).mul
        (a03RiemannZeta_measurable.comp ((hE.sub_const 1).add hS))).div
          (a03RiemannZeta_measurable.comp hE) |>.mul
            ((a03EtaArithmetic_measurable_comp _ _ _ _ ha hU hV hS).mul
              (a03EtaArithmetic_measurable_comp _ _ _ _ hb hV hU hS))

theorem a03ZeroModeRatioArithmeticKernel_measurable_comp {Ω : Type*} [MeasurableSpace Ω]
    (α : MomentShifts) {a b : ℕ} (ha : a≠0) (hb : b≠0) {U V S : Ω→ℂ}
    (hU : Measurable U) (hV : Measurable V) (hS : Measurable S) :
    Measurable (fun x => a03ZeroModeRatioArithmeticKernel α a b (U x) (V x) (S x)) :=
  (a03ZeroModeRatioArithmeticNumerator_measurable_comp α ha hb hU hV hS).div (hU.mul hV)

end
end Sechstmoment.Source
