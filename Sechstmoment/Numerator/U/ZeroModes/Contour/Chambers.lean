import Mathlib.Analysis.Convolution
import Sechstmoment.Numerator.U.Separation.ShapeNormalization
import Sechstmoment.Numerator.U.Separation.SixTermOrientation


namespace Sechstmoment.Source
open Complex MeasureTheory
open scoped BigOperators
open Classical
noncomputable section

def a03ZeroModePairPermutation (m n : Bool) (j : Fin 4) : Fin 4 :=
  ![if m then 1 else 0, if m then 0 else 1,
    if n then 3 else 2, if n then 2 else 3] j

@[simp] theorem a03ZeroModePairPermutation_involutive (m n : Bool) (j : Fin 4) :
    a03ZeroModePairPermutation m n (a03ZeroModePairPermutation m n j) = j := by
  cases m <;> cases n <;> fin_cases j <;> norm_num [a03ZeroModePairPermutation]

def a03ZeroModeChamberShifts (m n : Bool) (α : MomentShifts) : MomentShifts :=
  fun j => α (a03ZeroModePairPermutation m n j)

@[simp] theorem a03ZeroModeChamberShifts_involutive (m n : Bool) (α : MomentShifts) :
    a03ZeroModeChamberShifts m n (a03ZeroModeChamberShifts m n α) = α := by
  funext j
  simp [a03ZeroModeChamberShifts]

def a03ZeroModeReverseNegative (α : MomentShifts) : MomentShifts :=
  ![-α 3, -α 2, -α 1, -α 0]

@[simp] theorem a03ZeroModeReverseNegative_involutive (α : MomentShifts) :
    a03ZeroModeReverseNegative (a03ZeroModeReverseNegative α) = α := by
  funext j
  fin_cases j <;> simp [a03ZeroModeReverseNegative]

theorem a03ZeroMode_chamber_dual_partner (m n : Bool) (α : MomentShifts) :
    a03ZeroModeReverseNegative (a03ZeroModeChamberShifts m n α) =
      a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts α 1) := by
  funext j
  cases m <;> cases n <;> fin_cases j <;>
    simp [a03ZeroModeReverseNegative, a03ZeroModeChamberShifts,
      a03ZeroModePairPermutation, bblrSixShifts]

def a03ZeroModeContourPrefactor (α : MomentShifts) : ℂ :=
  riemannZeta (1+α 0-α 1)*riemannZeta (1+α 2-α 3)/
    riemannZeta (2+α 0-α 1+α 2-α 3)

theorem a03ZeroModeContourPrefactor_reverseNegative (α : MomentShifts) :
    a03ZeroModeContourPrefactor (a03ZeroModeReverseNegative α) =
      a03ZeroModeContourPrefactor α := by
  unfold a03ZeroModeContourPrefactor
  change riemannZeta (1 + -α 3 - -α 2)*riemannZeta (1 + -α 1 - -α 0)/
    riemannZeta (2 + -α 3 - -α 2 + -α 1 - -α 0) = _
  rw [show 1 + -α 3 - -α 2 = 1+α 2-α 3 by ring,
    show 1 + -α 1 - -α 0 = 1+α 0-α 1 by ring,
    show 2 + -α 3 - -α 2 + -α 1 - -α 0 = 2+α 0-α 1+α 2-α 3 by ring,
    mul_comm]

theorem a03ZeroMode_chamber_phase_dual_partner (m n : Bool) (α : MomentShifts) :
    bblrSixPhaseExponents α 1 -
      (a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts α 1) 1)-
      (a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts α 1) 3) =
      -(a03ZeroModeChamberShifts m n α 1)-(a03ZeroModeChamberShifts m n α 3) := by
  cases m <;> cases n <;>
    simp [a03ZeroModeChamberShifts, a03ZeroModePairPermutation,
      bblrSixShifts, bblrSixPhaseExponents] <;> ring

theorem a03ZeroMode_verticalIntegral_reflection (c : ℝ) (F : ℂ → ℂ) :
    verticalIntegral c (fun z => F (-z)) = verticalIntegral (-c) F := by
  unfold verticalIntegral
  congr 1
  calc
    (∫ v : ℝ, F (-((c:ℂ)+(v:ℂ)*I))) =
        ∫ v : ℝ, F (((-c:ℝ):ℂ)+((-v:ℝ):ℂ)*I) := by
      apply integral_congr_ae
      filter_upwards [] with v
      congr 1
      push_cast
      ring
    _ = _ := MeasureTheory.integral_neg_eq_self
      (fun v : ℝ => F (((-c:ℝ):ℂ)+(v:ℂ)*I)) volume

theorem a03ZeroMode_verticalIntegral_reflection_div (c : ℝ) (F : ℂ → ℂ) :
    verticalIntegral c (fun z => F (-z)/z) =
      -verticalIntegral (-c) (fun z => F z/z) := by
  have he : (fun z : ℂ => F (-z)/z) =
      (fun z : ℂ => -(F (-z)/(-z))) := by
    funext z
    simp only [div_eq_mul_inv, inv_neg, mul_neg, neg_neg]
  rw [he]
  unfold verticalIntegral
  rw [integral_neg]
  rw [mul_neg]
  congr 1
  have h := a03ZeroMode_verticalIntegral_reflection c (fun z => F z/z)
  unfold verticalIntegral at h
  exact h

end
end Sechstmoment.Source
