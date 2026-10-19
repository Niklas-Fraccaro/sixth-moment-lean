import Sechstmoment.Numerator.Polar.PoleKiller
import Sechstmoment.Numerator.U.ZeroModes.Contour.Chambers

/-! The same literal auxiliary weight in all four factor chambers. -/
namespace Sechstmoment
open Complex Source
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

/-- The quadratic killing factor depends only on the squared root. -/
def a03SquarePoleFactor (q z : ℂ) : ℂ := if q=0 then 1 else 1-z^2/q

theorem polarPoleKillingFactor_eq_square (ρ z : ℂ) :
    polarPoleKillingFactor ρ z=a03SquarePoleFactor (ρ^2) z := by
  by_cases hρ : ρ=0
  · simp [polarPoleKillingFactor,a03SquarePoleFactor,hρ]
  · simp [polarPoleKillingFactor,a03SquarePoleFactor,hρ,pow_ne_zero 2 hρ]

/-- Six different squared roots, each with its actual multiplicity four. -/
theorem a03PolarPoleKiller_six_factors (T : ℝ) (σ : MomentShifts) (z : ℂ) :
    polarPoleKiller T σ z=Complex.exp (z^2)*
      (a03SquarePoleFactor (((rawMomentShifts T σ 0+rawMomentShifts T σ 2)/2)^2) z*
       a03SquarePoleFactor (((rawMomentShifts T σ 0+rawMomentShifts T σ 3)/2)^2) z*
       a03SquarePoleFactor (((rawMomentShifts T σ 1+rawMomentShifts T σ 2)/2)^2) z*
       a03SquarePoleFactor (((rawMomentShifts T σ 1+rawMomentShifts T σ 3)/2)^2) z*
       a03SquarePoleFactor (((rawMomentShifts T σ 0-rawMomentShifts T σ 1)/2)^2) z*
       a03SquarePoleFactor (((rawMomentShifts T σ 2-rawMomentShifts T σ 3)/2)^2) z)^4 := by
  unfold polarPoleKiller
  simp_rw [polarPoleKillingFactor_eq_square]
  simp only [Fintype.prod_prod_type,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
  norm_num [purePolarRoot,purePolarLeft,purePolarRight,bblrSixShifts]
  ring_nf

/-- Raw normalization commutes with exchanging either original pair. -/
theorem a03_raw_shifts_chamber (T : ℝ) (m n : Bool) (σ : MomentShifts) :
    rawMomentShifts T (a03ZeroModeChamberShifts m n σ)=
      a03ZeroModeChamberShifts m n (rawMomentShifts T σ) := by
  funext j
  rfl

/-- No additional root-separation condition is needed for this identity. -/
theorem a03PolarPoleKiller_chamber (T : ℝ) (m n : Bool) (σ : MomentShifts) (z : ℂ) :
    polarPoleKiller T (a03ZeroModeChamberShifts m n σ) z=polarPoleKiller T σ z := by
  rw [a03PolarPoleKiller_six_factors,a03PolarPoleKiller_six_factors,a03_raw_shifts_chamber]
  cases m <;> cases n <;>
    norm_num [a03ZeroModeChamberShifts,a03ZeroModePairPermutation]
    <;> ring_nf

/-- Raw normalization commutes with all six literal shift tuples. -/
theorem a03_raw_shifts_six (T : ℝ) (σ : MomentShifts) (j : Fin 6) :
    rawMomentShifts T (bblrSixShifts σ j)=bblrSixShifts (rawMomentShifts T σ) j := by
  funext k
  fin_cases j <;> fin_cases k <;> simp [rawMomentShifts,bblrSixShifts] <;> ring

/-- Each literal BBLR shift tuple preserves the same six squared roots. -/
theorem a03PolarPoleKiller_six (T : ℝ) (σ : MomentShifts) (j : Fin 6) (z : ℂ) :
    polarPoleKiller T (bblrSixShifts σ j) z=polarPoleKiller T σ z := by
  rw [a03PolarPoleKiller_six_factors,a03PolarPoleKiller_six_factors,a03_raw_shifts_six]
  fin_cases j <;> norm_num [bblrSixShifts] <;> ring_nf

theorem a03_raw_shifts_reverseNegative (T : ℝ) (σ : MomentShifts) :
    rawMomentShifts T (a03ZeroModeReverseNegative σ)=a03ZeroModeReverseNegative (rawMomentShifts T σ) := by
  funext j
  fin_cases j <;> simp [rawMomentShifts,a03ZeroModeReverseNegative] <;> ring

/-- The reverse-negative original/dual pairing uses exactly the same weight. -/
theorem a03PolarPoleKiller_reverseNegative (T : ℝ) (σ : MomentShifts) (z : ℂ) :
    polarPoleKiller T (a03ZeroModeReverseNegative σ) z=polarPoleKiller T σ z := by
  have he : a03ZeroModeReverseNegative σ=a03ZeroModeChamberShifts true true (bblrSixShifts σ 1) := by
    funext j
    fin_cases j <;> norm_num [a03ZeroModeReverseNegative,a03ZeroModeChamberShifts,
      a03ZeroModePairPermutation,bblrSixShifts]
  rw [he,a03PolarPoleKiller_chamber,a03PolarPoleKiller_six]

end
end Sechstmoment
