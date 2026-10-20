import SixthMoment.Numerator.U.ZeroModes.NativeGCDCoordinate
import SixthMoment.Numerator.U.ZeroModes.Ratio.SourceTimeBridge

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03NativeGCDCoordinateQuad_pos (w : Fin 5→ℕ) (hw : ∀ j,1≤w j)
    {X : ℝ} (hX : 0<X) (j : Fin 4) : 0<a03NativeGCDCoordinateQuad w X j := by
  have hp (j : Fin 5) : (0:ℝ)<w j := by exact_mod_cast (show 0<w j by have := hw j; omega)
  fin_cases j
  · exact hp 2
  · exact div_pos hX (mul_pos (hp 0) (hp 2))
  · exact hp 3
  · exact div_pos hX (mul_pos (hp 1) (hp 3))

theorem a03NativeGCDCoordinateArguments_quad (q : QuadraticScales)
    (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) (X : ℝ) (j : Fin 4) :
    a03NativeGCDCoordinateArguments false false q w X j.succ.succ=
      a03NativeGCDCoordinateQuad w X j/a03ZeroModeQuadScales q j := by
  have he (x : ℝ) (j : Fin 4) :
      a03SixZeroSourceArguments false false q w x j.succ.succ=rectangularZeroArguments q w x j.succ := by
    fin_cases j <;> rfl
  unfold a03NativeGCDCoordinateArguments
  rw [he,a03ZeroModePhysicalQuad_normalized,a03NativeGCDCoordinateQuad_eq q w hw]

theorem a03RatioEuclideanMultiplier_GCD_coordinate (α : MomentShifts)
    (q : QuadraticScales) (hq : ∀ j,0<q.size j) (w : Fin 5→ℕ) (hw : ∀ j,1≤w j)
    {X : ℝ} (hX : 0<X) :
    a03RatioEuclideanMultiplier α (Real.log (q.M₁/q.M₂)) (Real.log (q.N₁/q.N₂))
      (a03SixTensorLogPoint (a03NativeGCDCoordinateArguments false false q w X))=
      a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α) ((w 0:ℝ)*(w 2:ℝ)^2/X)*
        a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α) ((w 1:ℝ)*(w 3:ℝ)^2/X) := by
  have hM₁ : 0<q.M₁ := by simpa [QuadraticScales.size] using hq 2
  have hM₂ : 0<q.M₂ := by simpa [QuadraticScales.size] using hq 3
  have hN₁ : 0<q.N₁ := by simpa [QuadraticScales.size] using hq 4
  have hN₂ : 0<q.N₂ := by simpa [QuadraticScales.size] using hq 5
  have hp := a03NativeGCDCoordinateQuad_pos w hw hX
  have hc := a03NativeGCDCoordinateArguments_quad q w hw X
  have he := a03NativeGCDCoordinateQuad_ratio w hw hX
  rw [a03RatioEuclideanMultiplier_eq_partition]
  simp only [a03SixTensorLogPoint_apply]
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  norm_num only [a03ZeroModeQuadScales,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h0 h1 h2 h3
  erw [h0,h1,h2,h3,a03_ratio_exp_log_scaled hM₁ hM₂ (hp 0) (hp 1),
    a03_ratio_exp_log_scaled hN₁ hN₂ (hp 2) (hp 3),he.1,he.2]

def a03NativeRatioGCDCoordinateZeroMode (F : A03SixTensorSpace→ℂ)
    (ratioα : MomentShifts) (q : QuadraticScales) (a b : ℕ→ℂ) : ℂ :=
  ∑ w∈quadraticMainIndexSet q,a (w 0)*b (w 1)*(a03NativeGCDCoordinateScale w:ℂ)*
    ∫ X : ℝ in Ioi 0,(∏ j : Fin 5,
      (rectangularSmoothBlockWeight (a03NativeGCDCoordinateArguments false false q w X j.succ):ℂ))*
        (a03ZeroModeRatioPartition (a03ZeroModeRatioWeight ratioα) ((w 0:ℝ)*(w 2:ℝ)^2/X)*
          a03ZeroModeRatioPartition (a03ZeroModeRatioWeight ratioα) ((w 1:ℝ)*(w 3:ℝ)^2/X))*
            F (a03SixTensorLogPoint (a03NativeGCDCoordinateArguments false false q w X))

theorem a03_native_ratio_physical_zero_eq_GCD (F : A03SixTensorSpace→ℂ)
    (ratioα : MomentShifts) (q : QuadraticScales) (hq : ∀ j,0<q.size j) (a b : ℕ→ℂ) :
    a03SixTensorPhysicalZeroMode (fun y => a03RatioEuclideanMultiplier ratioα
      (Real.log (q.M₁/q.M₂)) (Real.log (q.N₁/q.N₂)) y*F y) false false q a b=
      a03NativeRatioGCDCoordinateZeroMode F ratioα q a b := by
  rw [a03_native_physical_zero_eq_GCD_coordinate]
  unfold a03NativeGCDCoordinateZeroMode a03NativeRatioGCDCoordinateZeroMode
  apply Finset.sum_congr rfl
  intro w hw
  have hp : ∀ j,1≤w j := fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX
  rw [a03RatioEuclideanMultiplier_GCD_coordinate ratioα q hq w hp hX]
  ring

end
end SixthMoment
