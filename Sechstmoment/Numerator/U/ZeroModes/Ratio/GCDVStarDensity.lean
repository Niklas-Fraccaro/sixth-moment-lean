import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.CoordinateDensity

/-! The retained actual GCD V* expression with all seven dyadic masks
and the finite amplifier profiles displayed separately from the exact
complex shifted arithmetic density. -/
namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def a03NativeGCDAllDyadicWeight (q : QuadraticScales) (w : Fin 5→ℕ) (X : ℝ) : ℝ :=
  rectangularSmoothBlockWeight ((w 0:ℝ)/q.A)*rectangularSmoothBlockWeight ((w 1:ℝ)/q.B)*
    ∏ j : Fin 5,rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments false false q w X j.succ)

def a03RetainedRatioGCDVStarExpandedZeroMode (dual : Bool) (Φ : ℝ→ℂ) (T : ℝ)
    (σ α : MomentShifts) (sg : ℝ) (q : QuadraticScales) (f g : ℝ→ℝ) : ℂ :=
  ∑ w∈quadraticMainIndexSet q,∫ X : ℝ in Ioi 0,
    (a03NativeGCDAllDyadicWeight q w X:ℂ)*
      (f (Real.log (w 0:ℝ)/Real.log T):ℂ)*(g (Real.log (w 1:ℝ)/Real.log T):ℂ)*
        (Nat.gcd (w 0*w 2) (w 1*w 3):ℂ)*
          (w 0:ℂ)^(-1+α 1)*(w 1:ℂ)^(-1+α 3)*(w 2:ℂ)^(-1-α 0+α 1)*
            (w 3:ℂ)^(-1-α 2+α 3)*(X:ℂ)^(-1-α 1-α 3)*
              (a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((w 0:ℝ)*(w 2:ℝ)^2/X)*
                a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((w 1:ℝ)*(w 3:ℝ)^2/X))*
                  ∫ t : ℝ,Complex.exp (((-(T*sg*(Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)*w 4/X):ℝ):ℂ)*I*(t:ℂ))*
                    a03RatioLeadingBranchProfile dual Φ T σ t*
                      bblrVStar (polarPoleKiller T σ) (X^2/((w 0:ℝ)*w 1*(T*t)^2))

/-- Every actual amplifier square root is consumed in the proved positive
complex-power density, while every actual dyadic mask remains. -/
theorem a03_actual_retained_ratio_GCD_VStar_eq_expanded (dual : Bool) (Φ : ℝ→ℂ)
    (T : ℝ) (σ α : MomentShifts) (sg : ℝ) (q : QuadraticScales) (f g : ℝ→ℝ) :
    a03RetainedRatioGCDVStarZeroMode dual Φ T σ α sg q
      (phaseActualAmplifierCoefficient T f q.A) (phaseActualAmplifierCoefficient T g q.B)=
      a03RetainedRatioGCDVStarExpandedZeroMode dual Φ T σ α sg q f g := by
  unfold a03RetainedRatioGCDVStarZeroMode a03RetainedRatioGCDVStarExpandedZeroMode
  apply Finset.sum_congr rfl
  intro w hw
  have hp : ∀ j,1≤w j := fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
  rw [←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  have he := a03_native_GCD_amplifier_density T q.A q.B f g α w hp hX
  let mask : ℂ := ∏ j : Fin 5,
    (rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments false false q w X j.succ):ℂ)
  let ratio : ℂ := a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((w 0:ℝ)*(w 2:ℝ)^2/X)*
    a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((w 1:ℝ)*(w 3:ℝ)^2/X)
  let time : ℂ := ∫ t : ℝ,Complex.exp (((-(T*sg*(Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)*w 4/X):ℝ):ℂ)*I*(t:ℂ))*
    a03RatioLeadingBranchProfile dual Φ T σ t*bblrVStar (polarPoleKiller T σ) (X^2/((w 0:ℝ)*w 1*(T*t)^2))
  change (phaseActualAmplifierCoefficient T f q.A (w 0)*phaseActualAmplifierCoefficient T g q.B (w 1)*
    (a03NativeGCDCoordinateScale w:ℂ))*(mask*ratio*(a03ZeroModeRealQuadDenominator α 0 (a03NativeGCDCoordinateQuad w X))⁻¹*time)=_
  calc
    _=(phaseActualAmplifierCoefficient T f q.A (w 0)*phaseActualAmplifierCoefficient T g q.B (w 1)*
        (a03NativeGCDCoordinateScale w:ℂ)*(a03ZeroModeRealQuadDenominator α 0 (a03NativeGCDCoordinateQuad w X))⁻¹)*
          mask*ratio*time := by ring
    _=_ := by
      rw [he]
      unfold a03NativeGCDAllDyadicWeight
      simp only [Complex.ofReal_mul,Complex.ofReal_prod]
      dsimp only [mask,ratio,time]
      ring

end
end Sechstmoment
