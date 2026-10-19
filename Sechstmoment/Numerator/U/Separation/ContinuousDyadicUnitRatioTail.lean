import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.GCDContinuousUnitRatioTail

/-! Completing the actual nonunit dyadic partition requires the whole
real interval up to 4/3. Its genuine ratio tail has a fixed factor 9/16. -/
namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem a03CommonX_integrated_bounded_ratio_lower {A m X L : ℝ}
    (hA : 0<A) (hm : 0<m) (hX : 0<X) (hL : 0<L) (hunit : X/(A*m)≤L) :
    X/(L^2*A)≤A*m^2/X := by
  have hXm : X≤L*(A*m) := (div_le_iff₀ (mul_pos hA hm)).mp hunit
  have hu : X/(A*(L*m))≤1 := (div_le_one (mul_pos hA (mul_pos hL hm))).mpr (by nlinarith)
  have hb := a03CommonX_integrated_unit_ratio_lower hA (mul_pos hL hm) hX hu
  have hh : X/A≤L^2*(A*m^2/X) := by convert hb using 1; ring
  apply (le_div_iff₀ hX).mpr
  have he : X/(L^2*A)=(X/A)/L^2 := by ring
  rw [he]
  have hstep : (X/A)/L^2≤A*m^2/X := (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    (by simpa only [mul_comm] using hh)
  have hh' := mul_le_mul_of_nonneg_right hstep hX.le
  have hcancel : (A*m^2/X)*X=A*m^2 := div_mul_cancel₀ _ hX.ne'
  simpa only [hcancel] using hh'

theorem a03CommonX_integrated_bounded_polynomial_ratio {T A m X a s L : ℝ}
    (hT : 0<T) (hA : 0<A) (hm : 0<m) (hX : 0<X) (hL : 0<L)
    (hAmp : A≤T^a) (hLow : T^(1-s)≤X) (hunit : X/(A*m)≤L) :
    (1/L^2)*T^(1-s-a)≤A*m^2/X := by
  have hp : 0<T^a := Real.rpow_pos_of_pos hT _
  have hh : T^(1-s)/T^a≤X/A := div_le_div₀ hX.le hLow hA hAmp
  rw [←Real.rpow_sub hT] at hh
  have hb := a03CommonX_integrated_bounded_ratio_lower hA hm hX hL hunit
  apply le_trans ?_ hb
  have hscale := mul_le_mul_of_nonneg_left hh (by positivity : (0:ℝ)≤1/L^2)
  convert hscale using 1
  ring

/-- The exact integrated-unit dyadic interval is covered by an arbitrary
uniform actual ratio power tail. -/
theorem a03CommonX_integrated_dyadic_unit_actualRatio_uniform_rapid {κ a s : ℝ}
    (hκ : 0<κ) (hmargin : 0<1-s-a) (M : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ A m X : ℝ,0<A → 0<m → 0<X → A≤T^a → T^(1-s)≤X → X/(A*m)≤4/3 →
        ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) (A*m^2/X)‖≤
          C*T^(-(M:ℝ)) := by
  obtain ⟨C,hC,hb⟩ := a03ActualRatioPartition_uniform_polynomial_tail hκ hmargin
    (show (0:ℝ)<9/16 by norm_num) M
  refine ⟨C,hC,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with T hb hT
  intro σ hroot A m X hA hm hX hAmp hLow hunit
  apply hb σ hroot
  have hl := a03CommonX_integrated_bounded_polynomial_ratio hT hA hm hX
    (show (0:ℝ)<4/3 by norm_num) hAmp hLow hunit
  norm_num at hl
  exact hl

end
end Sechstmoment
