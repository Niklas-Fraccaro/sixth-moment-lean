import Sechstmoment.Numerator.U.Sources.PassiveNativeSourceWitness
import Sechstmoment.Numerator.U.ZeroModes.GCDMasks.ActualGridPartition

/-! A genuinely supported common-X point in the low-gap region supplies the
passive source witness. No discrete quadratic relation is inferred. -/
namespace Sechstmoment
open Complex Real Source Set
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1000000

theorem a03_native_GCD_low_gap_nonzero_weight_passive
    (T A B H η : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H)
    (w : Fin 5→ℕ) (X : ℝ) (hX : 0<X)
    (hw : a03NativeGCDAllDyadicWeight (phaseActualScales A B H k) w X≠0)
    (hf : f (Real.log (w 0:ℝ)/Real.log T)≠0)
    (hg : g (Real.log (w 1:ℝ)/Real.log T)≠0)
    (hlow : a03NativeGCDCoordinateGap w≤η*X) :
    A03ActualPassiveNearZeroBlock T A B H η f g k := by
  have hp := a03NativeGCDAllDyadicWeight_nonzero_positive _ w X hw
  have hparts := hw
  simp only [a03NativeGCDAllDyadicWeight,mul_ne_zero_iff] at hparts
  have ha : (w 0:ℂ)≠0 := by exact_mod_cast (show w 0≠0 by have := hp 0; omega)
  have hb : (w 1:ℂ)≠0 := by exact_mod_cast (show w 1≠0 by have := hp 1; omega)
  refine ⟨⟨w,a03NativeGCDAllDyadicWeight_nonzero_index _
    (boundaryActual_scales_pos A B H k hA hB hH) w X hw,X,hX,?_,?_,hparts.2,hlow⟩⟩
  · unfold phaseActualAmplifierCoefficient
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hparts.1.1)
      (Complex.ofReal_ne_zero.mpr hf)) (Complex.cpow_ne_zero_iff.mpr (Or.inl ha))
  · unfold phaseActualAmplifierCoefficient
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hparts.1.2)
      (Complex.ofReal_ne_zero.mpr hg)) (Complex.cpow_ne_zero_iff.mpr (Or.inl hb))


theorem a03_native_GCD_low_gap_nonzero_weight_witness
    (T A B H η : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H)
    (w : Fin 5→ℕ) (X : ℝ) (hX : 0<X)
    (hw : a03NativeGCDAllDyadicWeight (phaseActualScales A B H k) w X≠0)
    (hf : f (Real.log (w 0:ℝ)/Real.log T)≠0)
    (hg : g (Real.log (w 1:ℝ)/Real.log T)≠0)
    (hlow : a03NativeGCDCoordinateGap w≤η*X) :
    ∃ p : A03PassiveNativeZeroWitness T A B H η f g k,p.w=w ∧ p.X=X := by
  have hp := a03NativeGCDAllDyadicWeight_nonzero_positive _ w X hw
  have hparts := hw
  simp only [a03NativeGCDAllDyadicWeight,mul_ne_zero_iff] at hparts
  have ha : (w 0:ℂ)≠0 := by exact_mod_cast (show w 0≠0 by have := hp 0; omega)
  have hb : (w 1:ℂ)≠0 := by exact_mod_cast (show w 1≠0 by have := hp 1; omega)
  refine ⟨⟨w,a03NativeGCDAllDyadicWeight_nonzero_index _
    (boundaryActual_scales_pos A B H k hA hB hH) w X hw,X,hX,?_,?_,hparts.2,hlow⟩,rfl,rfl⟩
  · unfold phaseActualAmplifierCoefficient
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hparts.1.1)
      (Complex.ofReal_ne_zero.mpr hf)) (Complex.cpow_ne_zero_iff.mpr (Or.inl ha))
  · unfold phaseActualAmplifierCoefficient
    exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hparts.1.2)
      (Complex.ofReal_ne_zero.mpr hg)) (Complex.cpow_ne_zero_iff.mpr (Or.inl hb))

end
end Sechstmoment
