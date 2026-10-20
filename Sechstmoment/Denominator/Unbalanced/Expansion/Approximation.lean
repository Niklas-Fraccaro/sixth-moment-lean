import Sechstmoment.Denominator.Unbalanced.Expansion.BoundaryBounds
import Sechstmoment.Denominator.Unbalanced.Expansion.LeftBoundary

namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section

theorem d04OneSidedExpansion_uniform_eventually_bound {R ε : ℝ}
    (hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4) :
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ T : ℝ in atTop,
      ∀ t∈Icc T (2*T), ∀ σ : Fin 2 → ℂ, (∀ j, ‖σ j‖≤R) →
        ‖riemannZeta (d04NegativeZetaArguments T t σ 0)*
          riemannZeta (d04NegativeZetaArguments T t σ 1)-
          d04OneSidedRawSeries (T^3) (d04NegativeZetaArguments T t σ 0)
            (d04NegativeZetaArguments T t σ 1)‖ ≤ K*T^(-1+ε) := by
  obtain ⟨CL,hCL,hleft⟩ := d04OneSidedLeft_vertical_bound_requested hε hε1 hR
  obtain ⟨CR,hCR,hright⟩ := d04OneSidedRightTail_power_bound
  obtain ⟨CH,hCH,hhorizontal⟩ := d04OneSidedHorizontal_power_bound
  refine ⟨(CR+CL+CH+CH)/(2*Real.pi),by positivity,?_⟩
  filter_upwards [hleft,d04NormalizedShifts_uniform_eventually_small hR
    (by norm_num : (0 : ℝ)<1/4)] with T hleftT hsmall
  intro t ht σ hσ
  have hT : 4≤T := hsmall.1
  have hT0 : 0<T := by linarith
  have hraw : ∀ j, ‖σ j/(Real.log T : ℂ)‖≤1/4 := hsmall.2 σ hσ
  have hw0 := d04NegativeZetaArguments_height_window hT ht σ hraw 0
  have hw1 := d04NegativeZetaArguments_height_window hT ht σ hraw 1
  have ha : -1<(-1+ε/2) := by linarith
  have ha0 : (-1+ε/2)<0 := by linarith
  have hradius : 0<T/4 := by positivity
  have hs0 : T/4 < |(d04NegativeZetaArguments T t σ 0).im| := by
    linarith [hw0.2.1]
  have hs1 : T/4 < |(d04NegativeZetaArguments T t σ 1).im| := by
    linarith [hw1.2.1]
  have hbase := d04OneSidedRawSeries_error_norm_le (pow_pos hT0 3) ha ha0 hradius
    (d04NegativeZetaArguments T t σ 0) (d04NegativeZetaArguments T t σ 1)
    hs0 hs1 (by linarith [hw0.1.1]) (by linarith [hw1.1.1])
  have hRBound := hright T hT (d04NegativeZetaArguments T t σ 0)
    (d04NegativeZetaArguments T t σ 1)
    (by linarith [hw0.1.1]) (by linarith [hw1.1.1])
  have hTop := hhorizontal T (-1+ε/2) (T/4) hT ha.le ha0.le
    (abs_of_pos hradius) (d04NegativeZetaArguments T t σ 0)
    (d04NegativeZetaArguments T t σ 1) hw0.1.1 hw1.1.1
    hw0.2.1 hw0.2.2 hw1.2.1 hw1.2.2
  have hBottom := hhorizontal T (-1+ε/2) (-T/4) hT ha.le ha0.le
    (by rw [neg_div, abs_neg, abs_of_pos hradius])
    (d04NegativeZetaArguments T t σ 0) (d04NegativeZetaArguments T t σ 1)
    hw0.1.1 hw1.1.1 hw0.2.1 hw0.2.2 hw1.2.1 hw1.2.2
  have hpow : T^(-2 : ℝ)≤T^(-1+ε) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hRRequested := hRBound.trans (mul_le_mul_of_nonneg_left hpow hCR)
  have hTopRequested := hTop.trans (mul_le_mul_of_nonneg_left hpow hCH)
  have hBottomRequested := hBottom.trans (mul_le_mul_of_nonneg_left hpow hCH)
  have hBottom' : ‖d04OneSidedHorizontalIntegral (T^3)
      (d04NegativeZetaArguments T t σ 0) (d04NegativeZetaArguments T t σ 1)
      (-1+ε/2) (-(T/4))‖≤CH*T^(-1+ε) := by
    simpa only [neg_div] using hBottomRequested
  calc
    _ ≤ (1/(2*Real.pi))*(‖d04OneSidedRightTail (T^3)
          (d04NegativeZetaArguments T t σ 0) (d04NegativeZetaArguments T t σ 1) (T/4)‖+
        ‖d04OneSidedVerticalTruncated (T^3)
          (d04NegativeZetaArguments T t σ 0) (d04NegativeZetaArguments T t σ 1)
          (-1+ε/2) (T/4)‖+
        ‖d04OneSidedHorizontalIntegral (T^3)
          (d04NegativeZetaArguments T t σ 0) (d04NegativeZetaArguments T t σ 1)
          (-1+ε/2) (-(T/4))‖+
        ‖d04OneSidedHorizontalIntegral (T^3)
          (d04NegativeZetaArguments T t σ 0) (d04NegativeZetaArguments T t σ 1)
          (-1+ε/2) (T/4)‖) := hbase
    _ ≤ (1/(2*Real.pi))*(CR*T^(-1+ε)+CL*T^(-1+ε)+CH*T^(-1+ε)+CH*T^(-1+ε)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (add_le_add (add_le_add hRRequested (hleftT t ht σ hσ))
        hBottom') hTopRequested
    _ = _ := by ring

end
end Sechstmoment
