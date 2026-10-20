import Sechstmoment.Numerator.U.Separation.ActualGapPhase
import Sechstmoment.Numerator.U.Separation.ActualSeparatedMellinGrid
import Sechstmoment.Numerator.U.Separation.SeparatedPhaseRemainder

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def phaseActualScales (A B H : ℝ) (k : Fin 4 → ℕ) : QuadraticScales :=
  ⟨A,B,rectangularAFESmoothScale (k 0),rectangularAFESmoothScale (k 1),
    rectangularAFESmoothScale (k 2),rectangularAFESmoothScale (k 3),H⟩

def phaseActualAmplifierCoefficient (T : ℝ) (f : ℝ → ℝ) (A : ℝ) (a : ℕ) : ℂ :=
  (rectangularSmoothBlockWeight ((a:ℝ)/A):ℂ)*
    (f (Real.log (a:ℝ)/Real.log T):ℂ)*(a:ℂ)^(-(1/2:ℂ))

def phaseActualCommonFactor (T : ℝ) (Φ : ℝ → ℝ) (G : ℂ → ℂ)
    (α : MomentShifts) (t : ℝ) (k : Fin 4 → ℕ) (z : ℂ) : ℂ :=
  (Φ (t/T):ℂ)*(G z/z*bblrGammaQuotient t α z*(Real.pi:ℂ)^(-2*z))*
    ∏ j : Fin 4, (rectangularAFESmoothScale (k j):ℂ)^(-(1/2+α j+z))

def phaseActualKernelSummand (T A B H : ℝ) (f g Φ : ℝ → ℝ) (G : ℂ → ℂ)
    (α : MomentShifts) (u v : ℕ) (t : ℝ) (k n : Fin 4 → ℕ) (h : ℕ) (z : ℂ) : ℂ :=
  (rectangularSmoothBlockWeight ((u+1:ℝ)/A):ℂ)*
    (rectangularSmoothBlockWeight ((v+1:ℝ)/B):ℂ)*
    (rectangularSmoothBlockWeight ((h:ℝ)/H):ℂ)*rectangularMomentPairWeight T f g Φ u v t*
    ((rectangularAFESmoothWeight k n:ℂ)*rectangularAFEMellinKernel G α t n z)

private theorem actual_tuple_base (A B H : ℝ) (k n : Fin 4 → ℕ) (a b h : ℕ)
    (α : MomentShifts) (z : ℂ) :
    phaseBaseSmoothFactor (phaseActualScales A B H k) α z (rectangularAFESourceTuple a b n h)=
      (rectangularSmoothBlockWeight ((h:ℝ)/H):ℂ)*∏ j : Fin 4,
        rectangularActualMellinBlockWeight α z j ((n j+1:ℝ)/rectangularAFESmoothScale (k j)) := by
  unfold phaseBaseSmoothFactor
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  fin_cases j <;> simp [phaseQuadVariable,phaseQuadScale,phaseActualScales,rectangularAFESourceTuple]

private theorem actual_tuple_ratio (positive : Bool) (a b h : ℕ) (n : Fin 4 → ℕ) :
    rectangularGapSign positive*((rectangularAFESourceTuple a b n h 6):ℝ)/
      (((rectangularAFESourceTuple a b n h 1):ℝ)*
        rectangularAFESourceTuple a b n h 4*rectangularAFESourceTuple a b n h 5)=
      rectangularGapRatio positive b h n := by
  simp [rectangularAFESourceTuple,rectangularGapRatio,Nat.cast_mul]

theorem phaseActualKernelSummand_exact_phase (T A B H : ℝ) (f g Φ : ℝ → ℝ)
    (G : ℂ → ℂ) (α : MomentShifts) (u v : ℕ) (t : ℝ)
    (k n : Fin 4 → ℕ) (h : ℕ) (z : ℂ) :
    phaseActualKernelSummand T A B H f g Φ G α u v t k n h z=
      phaseActualCommonFactor T Φ G α t k z*
        (phaseActualAmplifierCoefficient T f A (u+1)*phaseActualAmplifierCoefficient T g B (v+1)*
          phaseBaseSmoothFactor (phaseActualScales A B H k) α z
            (rectangularAFESourceTuple (u+1) (v+1) n h))*
          rectangularTwistedQuadPhase t (u+1) (v+1) n := by
  unfold phaseActualKernelSummand
  rw [rectangular_actual_smooth_AFE_Mellin_weights]
  rw [actual_tuple_base]
  unfold phaseActualCommonFactor phaseActualAmplifierCoefficient
  push_cast
  have hp := rectangular_actual_pair_weight_oscillation T f g Φ u v t n
  calc
    _ = ((rectangularSmoothBlockWeight ((u+1:ℝ)/A):ℂ)*
      (rectangularSmoothBlockWeight ((v+1:ℝ)/B):ℂ)*
      (rectangularSmoothBlockWeight ((h:ℝ)/H):ℂ))*
      ((G z/z*bblrGammaQuotient t α z*(Real.pi:ℂ)^(-2*z))*
        ∏ j : Fin 4, (rectangularAFESmoothScale (k j):ℂ)^(-(1/2+α j+z)))*
      (∏ j : Fin 4, rectangularActualMellinBlockWeight α z j
        ((n j+1:ℝ)/rectangularAFESmoothScale (k j)))*
      (rectangularMomentPairWeight T f g Φ u v t*rectangularAFEOscillation t n) := by ring
    _ = _ := by rw [hp]; ring

theorem phaseActualKernelSummand_signed_phase (positive : Bool) (T A B H : ℝ)
    (f g Φ : ℝ → ℝ) (G : ℂ → ℂ) (α : MomentShifts) (u v : ℕ) (t : ℝ)
    (k n : Fin 4 → ℕ) (z : ℂ)
    (hn : if positive then rectangularPositiveQuadGap (u+1) (v+1) n
      else rectangularNegativeQuadGap (u+1) (v+1) n) :
    phaseActualKernelSummand T A B H f g Φ G α u v t k n
        (rectangularAFEGap positive (u+1) (v+1) n) z=
      phaseActualCommonFactor T Φ G α t k z*
        (phaseActualAmplifierCoefficient T f A (u+1)*phaseActualAmplifierCoefficient T g B (v+1)*
          phaseBaseSmoothFactor (phaseActualScales A B H k) α z
            (rectangularAFESourceTuple (u+1) (v+1) n
              (rectangularAFEGap positive (u+1) (v+1) n)))*
          (1+(rectangularGapRatio positive (v+1)
            (rectangularAFEGap positive (u+1) (v+1) n) n:ℂ))^(-(t:ℂ)*I) := by
  rw [phaseActualKernelSummand_exact_phase,
    rectangular_actual_signed_gap_phase positive (u+1) (v+1) (by omega) t n hn]

theorem phaseActualKernelSummand_five_weight_hasSum (positive : Bool) (T A B H : ℝ)
    (hB : 0<B) (hH : 0<H) (f g Φ : ℝ → ℝ) (G : ℂ → ℂ) (α : MomentShifts)
    (u v : ℕ) (t : ℝ) (k n : Fin 4 → ℕ) (z : ℂ)
    (hn : if positive then rectangularPositiveQuadGap (u+1) (v+1) n
      else rectangularNegativeQuadGap (u+1) (v+1) n)
    (hr : |rectangularGapRatio positive (v+1)
      (rectangularAFEGap positive (u+1) (v+1) n) n|<1) :
    HasSum (fun l : ℕ => phaseActualCommonFactor T Φ G α t k z*
      (phaseSeparationScalar (phaseActualScales A B H k) (rectangularGapSign positive) t l*
        (phaseActualAmplifierCoefficient T f A (u+1)*
          phaseAdjustedBeta (phaseActualScales A B H k) (phaseActualAmplifierCoefficient T g B) l (v+1)*
          ∏ i : Fin 5, phaseFiveWeights α z l i
            (rectangularWeightArguments (phaseActualScales A B H k)
              (rectangularAFESourceTuple (u+1) (v+1) n
                (rectangularAFEGap positive (u+1) (v+1) n)) i))))
      (phaseActualKernelSummand T A B H f g Φ G α u v t k n
        (rectangularAFEGap positive (u+1) (v+1) n) z) := by
  have hN₁ : 0<(phaseActualScales A B H k).N₁ := by
    dsimp [phaseActualScales,rectangularAFESmoothScale]; positivity
  have hN₂ : 0<(phaseActualScales A B H k).N₂ := by
    dsimp [phaseActualScales,rectangularAFESmoothScale]; positivity
  have hs := (phase_five_product_summand_hasSum (phaseActualScales A B H k) hB hH hN₁ hN₂
    α z (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
    (rectangularGapSign positive) t
    (rectangularAFESourceTuple (u+1) (v+1) n (rectangularAFEGap positive (u+1) (v+1) n))
    (by change 0<v+1; omega) (by change 0<n 2+1; omega) (by change 0<n 3+1; omega)
    (by rw [actual_tuple_ratio]; exact hr)).mul_left (phaseActualCommonFactor T Φ G α t k z)
  rw [phaseActualKernelSummand_signed_phase positive T A B H f g Φ G α u v t k n z hn]
  rw [actual_tuple_ratio] at hs
  have h₀ : rectangularAFESourceTuple (u+1) (v+1) n
      (rectangularAFEGap positive (u+1) (v+1) n) 0=u+1 := rfl
  have h₁ : rectangularAFESourceTuple (u+1) (v+1) n
      (rectangularAFEGap positive (u+1) (v+1) n) 1=v+1 := rfl
  simpa only [h₀,h₁,mul_assoc] using hs

end
end Sechstmoment
