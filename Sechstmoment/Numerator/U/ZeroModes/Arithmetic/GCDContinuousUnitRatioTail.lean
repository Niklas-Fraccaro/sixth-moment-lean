import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.GCDMaskTransport

/-! Uniform actual ratio tails for a omitted continuous integrated-unit
region of the unrestricted common-X integral. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem a03CommonX_integrated_unit_actualRatio_uniform_rapid {κ a s : ℝ}
    (hκ : 0<κ) (hmargin : 0<1-s-a) (M : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ A m X : ℝ,0<A → 0<m → 0<X → A≤T^a → T^(1-s)≤X → X/(A*m)≤1 →
        ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) (A*m^2/X)‖≤
          C*T^(-(M:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := a03ActualRatioPartition_uniform_polynomial_tail hκ hmargin
    (show (0:ℝ)<1 by norm_num) M
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with T hb hT
  intro σ hroot A m X hA hm hX hAmp hLow hunit
  apply hb σ hroot
  simpa only [one_mul] using a03CommonX_integrated_unit_polynomial_ratio hT hA hm hX hAmp hLow hunit

theorem a03Rectangular_continuous_unit_ratio_margin {a b s : ℝ}
    (ha : 0≤a) (hab : a≤b) (hrect : 3*a+5*b<2) (hs : s≤1/2) :
    0<1-s-a ∧ 0<1-s-b := by
  constructor <;> linarith

end
end Sechstmoment
