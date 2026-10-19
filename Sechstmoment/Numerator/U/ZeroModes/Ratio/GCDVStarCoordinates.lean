import Sechstmoment.Numerator.U.ZeroModes.NativeRatioGCD
import Sechstmoment.Numerator.U.ZeroModes.Ratio.FullVStarNative

/-! Literal retained BBLR ratio-GCD V* expression with real product
coordinate X, true gap d*h/X and all native dyadic masks. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03NativeGCDCoordinate_linear_gap (q : QuadraticScales)
    (hq : ∀ j,0<q.size j) (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) {X : ℝ} (hX : 0<X) :
    q.H/(q.B*(q.N₁*q.N₂))*Real.exp (a03SixGapLinear
      (a03SixTensorLogPoint (a03NativeGCDCoordinateArguments false false q w X)))=
      (Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)*w 4/X := by
  have hp (j : Fin 5) : (0:ℝ)<w j := by exact_mod_cast (show 0<w j by have := hw j; omega)
  have hd : (0:ℝ)<Nat.gcd (w 0*w 2) (w 1*w 3) :=
    a03ZeroMode_gcd_pos (by have := hw 0; omega) (by have := hw 1; omega)
      (by have := hw 2; omega) (by have := hw 3; omega)
  have hB : 0<q.B := by simpa [QuadraticScales.size] using hq 1
  have hH : 0<q.H := by simpa [QuadraticScales.size] using hq 6
  have hN₁ : 0<q.N₁ := by simpa [QuadraticScales.size] using hq 4
  have hN₂ : 0<q.N₂ := by simpa [QuadraticScales.size] using hq 5
  have hargs := a03SixZeroSourceArguments_positive false false q hq w hw
    (mul_pos (a03NativeGCDCoordinateScale_pos w hw) hX)
  erw [a03SixGapLinear_logPoint_exp _ hargs]
  simp [a03SixZeroSourceArguments,a03SixZeroPairArguments,
    rectangularZeroArguments,a03NativeGCDCoordinateScale]
  field_simp [hB.ne',hH.ne',hN₁.ne',hN₂.ne',hd.ne',(hp 0).ne',(hp 1).ne',(hp 2).ne',(hp 3).ne',hX.ne']

theorem a03ZeroModePermutedPhysicalQuad_false_false (q : QuadraticScales) (w : Fin 5→ℕ) (x : ℝ) :
    a03ZeroModePermutedPhysicalQuad false false q w x=a03ZeroModePhysicalQuad q w x := by
  ext j
  fin_cases j <;> rfl

def a03RetainedRatioGCDVStarZeroMode (dual : Bool) (Φ : ℝ→ℂ) (T : ℝ)
    (σ α : MomentShifts) (sg : ℝ) (q : QuadraticScales) (a b : ℕ→ℂ) : ℂ :=
  ∑ w∈quadraticMainIndexSet q,a (w 0)*b (w 1)*(a03NativeGCDCoordinateScale w:ℂ)*
    ∫ X : ℝ in Ioi 0,
      (∏ j : Fin 5,(rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments false false q w X j.succ):ℂ))*
        (a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((w 0:ℝ)*(w 2:ℝ)^2/X)*
          a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) ((w 1:ℝ)*(w 3:ℝ)^2/X))*
            (a03ZeroModeRealQuadDenominator α 0 (a03NativeGCDCoordinateQuad w X))⁻¹*
              ∫ t : ℝ,Complex.exp (((-(T*sg*(Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)*w 4/X):ℝ):ℂ)*I*(t:ℂ))*
                a03RatioLeadingBranchProfile dual Φ T σ t*
                  bblrVStar (polarPoleKiller T σ) (X^2/((w 0:ℝ)*w 1*(T*t)^2))

/-- Exact positive-real BBLR product substitution in the literal actual
V* zero mode. Every native finite range and mask remains visible. -/
theorem a03_actual_ratio_VStar_zero_eq_retained_GCD (dual : Bool) (Φ : ℝ→ℂ) (T : ℝ)
    (σ α : MomentShifts) (sg : ℝ) (q : QuadraticScales) (hq : ∀ j,0<q.size j) (a b : ℕ→ℂ) :
    a03PhysicalActualRatioLinearVStarZeroMode dual Φ T σ α
      (Real.log (q.M₁/q.M₂)) (Real.log (q.N₁/q.N₂)) (q.H/(q.B*(q.N₁*q.N₂))) sg false false q a b=
      a03RetainedRatioGCDVStarZeroMode dual Φ T σ α sg q a b := by
  unfold a03PhysicalActualRatioLinearVStarZeroMode a03PhysicalLinearVStarZeroMode
    a03RetainedRatioGCDVStarZeroMode
  apply Finset.sum_congr rfl
  intro w hw
  have hp : ∀ j,1≤w j := fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
  let F : ℝ→ℂ := fun x =>
    let y := a03SixTensorLogPoint (a03SixZeroSourceArguments false false q w x)
    let Q := a03ZeroModePermutedPhysicalQuad false false q w x
    a03PhysicalZeroSmoothMask false false q w x*
      a03RatioEuclideanMultiplier (rawMomentShifts T σ) (Real.log (q.M₁/q.M₂)) (Real.log (q.N₁/q.N₂)) y*
        (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*
          ∫ t : ℝ,Complex.exp (((-(T*sg*(q.H/(q.B*(q.N₁*q.N₂)))*Real.exp (a03SixGapLinear y)):ℝ):ℂ)*I*(t:ℂ))*
            a03RatioLeadingBranchProfile dual Φ T σ t*bblrVStar (polarPoleKiller T σ) (a03PhysicalQuadProduct Q/(T*t)^2)
  change a (w 0)*b (w 1)*(∫ x : ℝ in Ioi 0,F x)=_
  have he := integral_comp_mul_left_Ioi' F (0:ℝ) (a03NativeGCDCoordinateScale_pos w hp)
  simp only [mul_zero,Complex.real_smul] at he
  rw [←he]
  simp only [←mul_assoc]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  unfold F
  simp only [a03ZeroModePermutedPhysicalQuad_false_false,a03NativeGCDCoordinateQuad_eq q w hp]
  change a03PhysicalZeroSmoothMask false false q w (a03NativeGCDCoordinateScale w*X)*
    a03RatioEuclideanMultiplier (rawMomentShifts T σ) (Real.log (q.M₁/q.M₂)) (Real.log (q.N₁/q.N₂))
      (a03SixTensorLogPoint (a03NativeGCDCoordinateArguments false false q w X))*
    (a03ZeroModeRealQuadDenominator α 0 (a03NativeGCDCoordinateQuad w X))⁻¹*(∫ t : ℝ,_)=_
  rw [a03RatioEuclideanMultiplier_GCD_coordinate _ q hq w hp hX]
  unfold a03PhysicalQuadProduct
  rw [a03NativeGCDCoordinateQuad_product w hp X]
  unfold a03PhysicalZeroSmoothMask
  congr 1
  · unfold a03NativeGCDCoordinateArguments
    ring
  · apply integral_congr_ae
    apply ae_of_all
    intro t
    have hgap := a03NativeGCDCoordinate_linear_gap q hq w hp hX
    have hegap : T*sg*(q.H/(q.B*(q.N₁*q.N₂)))*Real.exp (a03SixGapLinear
        (a03SixTensorLogPoint (a03NativeGCDCoordinateArguments false false q w X)))=
          T*sg*(Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)*w 4/X := by
      calc
        _=(T*sg)*((q.H/(q.B*(q.N₁*q.N₂)))*Real.exp (a03SixGapLinear
            (a03SixTensorLogPoint (a03NativeGCDCoordinateArguments false false q w X)))) := by ring
        _=_ := by rw [hgap]; ring
    dsimp only
    erw [hegap]
    simp only [div_div]

/-- Genuine full-Mellin reconstruction in the retained ratio-GCD
coordinate, with the actual ratio multiplier and the actual primary G. -/
theorem a03_actual_ratio_native_full_eq_retained_GCD_VStar
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hL : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ α : MomentShifts) (hroot : ∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hα : ∀ j,‖α j‖≤1/4) (dual : Bool) (sg : ℝ)
    (q : QuadraticScales) (hq : ∀ j,0<q.size j) (a b : ℕ→ℂ) :
    (1/(2*Real.pi):ℂ)*(∫ v : ℝ,a03SourceSpectralActualRatioLinearZero dual Φ T c σ α
      (Real.log (q.M₁/q.M₂)) (Real.log (q.N₁/q.N₂)) (q.H/(q.B*(q.N₁*q.N₂))) sg false false q a b v)=
      a03RetainedRatioGCDVStarZeroMode dual Φ T σ α sg q a b := by
  rw [a03SourceSpectralActualRatioLinearZero_full_eq_VStar hΦ hSupp hT hL hc hκ σ α hroot hα
    dual (Real.log (q.M₁/q.M₂)) (Real.log (q.N₁/q.N₂)) (q.H/(q.B*(q.N₁*q.N₂))) sg false false q hq a b]
  exact a03_actual_ratio_VStar_zero_eq_retained_GCD dual Φ T σ α sg q hq a b

end
end Sechstmoment
