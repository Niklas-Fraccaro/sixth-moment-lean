import Sechstmoment.Numerator.Shared.MomentHolomorphy
import Sechstmoment.Numerator.V.DP.DPRegularHolomorphy

/-!
# Genuine transfer of the actual DP moment to coincident shifts

The source sharp estimate is used only on the explicitly separated compact
product of circles. Both the actual moment and its actual fixed-circle main
term have independently proved holomorphy. The iterated maximum principle
therefore transfers the error to the whole polydisc, including zero shifts.
-/
namespace Sechstmoment.Source
open Complex MeasureTheory Set Polynomial Filter
open scoped Topology
noncomputable section

theorem dpActualMoment_coincident_uniform_smoothing (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X]) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ ∈ rectangularClosedPolydisc dpCauchyRadii,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → (∀ x, |deriv Φ x| ≤ B) →
      ‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ-
        (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpRegularLeadingDensity T η P σ‖ ≤
          C*T*(Real.log T)^8 := by
  obtain ⟨C,hC,hbound⟩ := dpActualMoment_regular_boundary_bound hsource η hη hηu P B hB
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16 : ℝ))]
    with T hbound hT hL σ hσ Φ hΦ hderiv
  have hR : ∀ j, 2*dpCauchyRadii j < Real.log T := by
    intro j
    have hr : dpCauchyRadii j ≤ (8 : ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
    linarith
  have hm := chiTwistedFourthMoment_differentiableOn_polydisc hT dpCauchyRadii hR
    η η (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ
    (dpProfile_zero_above η P) (dpProfile_zero_above η P) hΦ
  have hf := hm.sub ((dpRegularLeadingDensity_differentiableOn hη.le T P).const_mul
    ((T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))))
  exact rectangular_polydisc_norm_le dpCauchyRadii dpCauchyRadii_positive _ hf
    (fun τ hτ => hbound τ hτ Φ hΦ hderiv) σ hσ

theorem smoothDyadicWeight_deriv_bound (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |deriv Φ x| ≤ B := by
  have hs : HasCompactSupport Φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hΦ.2
  obtain ⟨B,hB⟩ := hs.deriv.exists_bound_of_continuous (hΦ.1.continuous_deriv (by simp))
  refine ⟨max B 0,le_max_right _ _,?_⟩
  intro x
  have hx : |deriv Φ x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
  exact hx.trans (le_max_left _ _)

theorem dpActualMoment_coincident_normalized_tendsto (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (σ : MomentShifts)
    (hσ : σ ∈ rectangularClosedPolydisc dpCauchyRadii) :
    Tendsto (fun T : ℝ => chiTwistedFourthMoment T (rawMomentShifts T σ)
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ/
      ((T : ℂ)*(Real.log T : ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpRegularKernel η P σ)) := by
  obtain ⟨B,hB,hderiv⟩ := smoothDyadicWeight_deriv_bound Φ hΦ
  obtain ⟨C,_,hbound⟩ := dpActualMoment_coincident_uniform_smoothing hsource η hη hηu P B hB
  let E : ℝ → ℂ := fun T => chiTwistedFourthMoment T (rawMomentShifts T σ)
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ-
      (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpRegularLeadingDensity T η P σ
  have hE := logNormalizedRemainder_tendsto E C
    (hbound.mono (fun T h => h σ hσ Φ hΦ hderiv))
  have ht := (tendsto_const_nhds (x := (arithmeticFactor : ℂ)*
    (∫ x : ℝ, (Φ x : ℂ))*dpRegularKernel η P σ)).add hE
  simp only [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hT0 : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hT).ne'
  have hL0 : (Real.log T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne'
  dsimp [E,dpRegularLeadingDensity]
  field_simp
  ring

theorem dpActualMoment_zero_shifts_normalized_tendsto (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => chiTwistedFourthMoment T (rawMomentShifts T 0)
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ/
      ((T : ℂ)*(Real.log T : ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*dpRegularKernel η P 0)) :=
  dpActualMoment_coincident_normalized_tendsto hsource η hη hηu P Φ hΦ 0
    dpCauchyPolydisc_contains_zero

end
end Sechstmoment.Source
