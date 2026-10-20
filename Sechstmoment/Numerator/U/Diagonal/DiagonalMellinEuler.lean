import Sechstmoment.Numerator.Polar.EulerMellinKernel
import Sechstmoment.Numerator.U.Diagonal.DiagonalEulerProduct


namespace Sechstmoment
open Complex
open scoped BigOperators

set_option maxHeartbeats 0

theorem polarMellinTriples_initial_re_lower_bound {α : MomentShifts} {δ : ℝ}
    {u v z : ℂ} (hδ : 0 < δ) (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) (hz : δ ≤ z.re) :
    (∀ i : Fin 3, δ/2 ≤ (polarMellinLeftTriple α u z i).re) ∧
    (∀ i : Fin 3, δ/2 ≤ (polarMellinRightTriple α v z i).re) := by
  have hre (j : Fin 4) : -(δ/4) ≤ (α j).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
  constructor <;> intro i <;> fin_cases i <;>
    simp [polarMellinLeftTriple, polarMellinRightTriple] <;>
    linarith [hre 0, hre 1, hre 2, hre 3]

theorem polarMellinDiagonal_norm_summable {α : MomentShifts} {δ : ℝ}
    {u v z : ℂ} (hδ : 0 < δ) (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) (hz : δ ≤ z.re) :
    Summable (fun n => ‖shiftedDiagonalArithmetic (polarMellinLeftTriple α u z)
      (polarMellinRightTriple α v z) 1 n‖) := by
  obtain ⟨ha,hb⟩ := polarMellinTriples_initial_re_lower_bound hδ hα hu hv hz
  exact shiftedDiagonalArithmetic_norm_summable (by linarith : 0 < δ/2) ha hb

theorem polarMellinDiagonal_eq_entangled_mul_pure {T : ℝ} {σ : MomentShifts}
    (m : Fin 6) {δ : ℝ} {u v z : ℂ} (hδ : 0 < δ)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) (hz : δ ≤ z.re) :
    (∑' n, shiftedDiagonalArithmetic
      (polarMellinLeftTriple (Source.bblrSixShifts (rawMomentShifts T σ) m) u z)
      (polarMellinRightTriple (Source.bblrSixShifts (rawMomentShifts T σ) m) v z) 1 n) =
      polarArithmeticEntangledFactor (Source.bblrSixShifts (rawMomentShifts T σ) m) u v z*
        purePolarZetaProduct T σ m z := by
  have hshift (j : Fin 4) :
      ‖Source.bblrSixShifts (rawMomentShifts T σ) m j‖ ≤ δ/4 :=
    bblrSixShifts_norm_le _ hα m j
  obtain ⟨ha,hb⟩ := polarMellinTriples_initial_re_lower_bound hδ hshift hu hv hz
  rw [shiftedDiagonalArithmetic_eq_zetaProduct_mul_rest (by linarith : 0 < δ/2) ha hb,
    polarNineZetaProduct_eq_entangled_mul_pure]
  unfold polarArithmeticEntangledFactor
  ring

end Sechstmoment
