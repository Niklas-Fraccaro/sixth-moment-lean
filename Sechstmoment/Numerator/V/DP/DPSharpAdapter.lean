import Sechstmoment.Numerator.V.DP.DPCoincidentTransfer

/-! Derive the earlier fixed smooth DP source interface from the literal
sharp-endpoint input, using proved partial summation and phase replacement.
Thus the fixed smooth interface introduces no additional analytical input. -/

namespace Sechstmoment.Source
open Complex MeasureTheory Set Polynomial Filter
open scoped Topology
noncomputable section

theorem dpRawMainTerm_eq_weighted_sharp (T η : ℝ) (P : ℝ[X]) (Φ : ℝ → ℝ)
    (σ : MomentShifts) :
    dpRawMainTerm T η P Φ (rawMomentShifts T σ) =
      (∫ x : ℝ, (Φ x : ℂ))*dpRawSharpMainTerm T T η P σ := by
  unfold dpRawMainTerm dpRawSharpMainTerm
  push_cast
  ring

theorem dpSharpInput_implies_fixed_smooth_input (hsource : DPv2SharpInput) :
    DPv2Input := by
  intro η hη hηu P Φ hΦ K hK hsep
  obtain ⟨B,hB,hderiv⟩ := smoothDyadicWeight_deriv_bound Φ hΦ
  obtain ⟨C,hC,hSmooth⟩ := dpActualMoment_uniform_smoothing hsource η hη hηu P K hK hsep B hB
  obtain ⟨D,hD,hslope⟩ := dpNormalizedFourSlope_compact_bound η P K hK hsep
  let E := 2*‖(arithmeticFactor : ℂ)‖*|η|^6*D*dpPhaseWindowConstant
  have hE : 0 ≤ E := by
    have := dpPhaseWindowConstant_nonneg
    dsimp [E]
    positivity
  let W : ℂ := ∫ x : ℝ, (Φ x : ℂ)
  refine ⟨C+‖W‖*E,add_nonneg hC (mul_nonneg (norm_nonneg _) hE),?_⟩
  filter_upwards [hSmooth,eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop dpPhaseWindowConstant)]
    with T hSmooth hT hL σ hσ
  have hp := dpRawSharpMainTerm_phase_bound hT hL
    (show T ∈ Icc (T/4) (2*T) from ⟨by linarith,by linarith⟩)
    hD η P σ (hslope σ hσ)
  have he : (T : ℂ)*W*dpLeadingDensity T η P σ-
      dpRawMainTerm T η P Φ (rawMomentShifts T σ) =
      -W*(dpRawSharpMainTerm T T η P σ-(T : ℂ)*dpLeadingDensity T η P σ) := by
    rw [dpRawMainTerm_eq_weighted_sharp]
    dsimp [W]
    ring
  calc
    _ ≤ ‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ-
        (T : ℂ)*W*dpLeadingDensity T η P σ‖+
      ‖(T : ℂ)*W*dpLeadingDensity T η P σ-
        dpRawMainTerm T η P Φ (rawMomentShifts T σ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ C*T*(Real.log T)^8+‖W‖*(E*T*(Real.log T)^8) := by
      apply add_le_add (hSmooth σ hσ Φ hΦ hderiv)
      rw [he,norm_mul,norm_neg]
      exact mul_le_mul_of_nonneg_left hp (norm_nonneg W)
    _ = _ := by ring

end
end Sechstmoment.Source
