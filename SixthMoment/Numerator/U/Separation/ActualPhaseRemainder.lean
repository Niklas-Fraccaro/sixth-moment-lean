import SixthMoment.Numerator.U.Separation.ActualSeparatedGap

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phaseActualKernelSummand_uniform_remainder {θ : ℝ} (hθ : 0≤θ) (M : ℝ) :
    ∃ L : ℝ, 0<L ∧ ∀ T : ℝ, Real.exp 1≤T →
      (⌈L*Real.log T⌉₊:ℝ)≤(L+1)*Real.log T ∧
      ∀ A B H : ℝ, 0<B → 0<H → ∀ f g Φ : ℝ → ℝ, ∀ G : ℂ → ℂ,
      ∀ α : MomentShifts, ∀ u v : ℕ, ∀ t : ℝ, ∀ k n : Fin 4 → ℕ,
      ∀ z : ℂ, ∀ positive : Bool,
      (if positive then rectangularPositiveQuadGap (u+1) (v+1) n
        else rectangularNegativeQuadGap (u+1) (v+1) n) → ∀ r : ℝ,
      |t|≤2*T → 0≤r → r≤1/4 → T*r≤θ*Real.log T →
      |rectangularGapRatio positive (v+1) (rectangularAFEGap positive (u+1) (v+1) n) n|≤r →
      ‖phaseActualKernelSummand T A B H f g Φ G α u v t k n
          (rectangularAFEGap positive (u+1) (v+1) n) z-
        ∑ l∈Finset.range ⌈L*Real.log T⌉₊, phaseActualCommonFactor T Φ G α t k z*
          (phaseSeparationScalar (phaseActualScales A B H k) (rectangularGapSign positive) t l*
            (phaseActualAmplifierCoefficient T f A (u+1)*
              phaseAdjustedBeta (phaseActualScales A B H k) (phaseActualAmplifierCoefficient T g B) l (v+1)*
              ∏ i : Fin 5, phaseFiveWeights α z l i
                (rectangularWeightArguments (phaseActualScales A B H k)
                  (rectangularAFESourceTuple (u+1) (v+1) n
                    (rectangularAFEGap positive (u+1) (v+1) n)) i)))‖≤
        ‖phaseActualCommonFactor T Φ G α t k z‖*
          ‖phaseActualAmplifierCoefficient T f A (u+1)*phaseActualAmplifierCoefficient T g B (v+1)*
            phaseBaseSmoothFactor (phaseActualScales A B H k) α z
              (rectangularAFESourceTuple (u+1) (v+1) n
                (rectangularAFEGap positive (u+1) (v+1) n))‖*T^(-M) := by
  obtain ⟨L,hL,hb⟩ := phase_five_product_uniform_remainder hθ M
  refine ⟨L,hL,?_⟩
  intro T hT
  refine ⟨(hb T hT).1,?_⟩
  intro A B H hB hH f g Φ G α u v t k n z positive hn r ht hr hr4 hTr hx
  have hN₁ : 0<(phaseActualScales A B H k).N₁ := by
    dsimp [phaseActualScales,rectangularAFESmoothScale]; positivity
  have hN₂ : 0<(phaseActualScales A B H k).N₂ := by
    dsimp [phaseActualScales,rectangularAFESmoothScale]; positivity
  let m := rectangularAFESourceTuple (u+1) (v+1) n (rectangularAFEGap positive (u+1) (v+1) n)
  have hm := (hb T hT).2 (phaseActualScales A B H k) hB hH hN₁ hN₂ α z
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
    (rectangularGapSign positive) t r ht hr hr4 hTr m
    (by change 0<v+1; omega) (by change 0<n 2+1; omega) (by change 0<n 3+1; omega)
    (by simpa [m,rectangularAFESourceTuple,rectangularGapRatio,Nat.cast_mul] using hx)
  have he : (rectangularGapSign positive*(m 6:ℝ)/((m 1:ℝ)*m 4*m 5))=
      rectangularGapRatio positive (v+1) (rectangularAFEGap positive (u+1) (v+1) n) n := by
    simp [m,rectangularAFESourceTuple,rectangularGapRatio,Nat.cast_mul]
  rw [he] at hm
  rw [phaseActualKernelSummand_signed_phase positive T A B H f g Φ G α u v t k n z hn,
    ← Finset.mul_sum,mul_assoc,← mul_sub,norm_mul]
  calc
    _ ≤ ‖phaseActualCommonFactor T Φ G α t k z‖*
      (‖phaseActualAmplifierCoefficient T f A (u+1)*phaseActualAmplifierCoefficient T g B (v+1)*
        phaseBaseSmoothFactor (phaseActualScales A B H k) α z m‖*T^(-M)) :=
      mul_le_mul_of_nonneg_left hm (norm_nonneg _)
    _ = _ := by dsimp [m]; ring

end
end SixthMoment
