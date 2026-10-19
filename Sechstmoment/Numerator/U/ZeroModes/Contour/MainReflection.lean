import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.EtaResidueArithmetic
import Sechstmoment.Numerator.U.ZeroModes.ResidueLabels

/-! Reflection of the literal finite-amplifier source M-contour. The required
M-identity is derived from η arithmetic; it is never a hypothesis. This file
establishes the difference of the two vertical lines. Moving those lines and
identifying the native GCD expression with this contour remain separate work. -/

namespace Sechstmoment.Source
open Complex MeasureTheory
open scoped BigOperators
open Classical
noncomputable section

def a03ZeroModeMainKernel (G : ℂ → ℂ) (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    (α : MomentShifts) (s : ℂ) : ℂ :=
  G s/s*a03EtaMainFunction N₁ N₂ a b α s

theorem a03ZeroMode_chamber_norm_le (m n : Bool) {α : MomentShifts} {R : ℝ}
    (hα : ∀ j : Fin 4, ‖α j‖≤R) :
    ∀ j : Fin 4, ‖a03ZeroModeChamberShifts m n α j‖≤R := by
  intro j
  exact hα (a03ZeroModePairPermutation m n j)

/-- The actual M-arithmetic supplies the source reflection, including the
sign supplied by `1/s`; no extra M-identity is accepted. -/
theorem a03ZeroModeMainKernel_reverseNegative (G : ℂ → ℂ)
    (hEven : ∀ z, G (-z)=G z) (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    {α : MomentShifts} (hα : ∀ j : Fin 4, ‖α j‖≤1/8) (s : ℂ) :
    a03ZeroModeMainKernel G N₁ N₂ a b (a03ZeroModeReverseNegative α) s =
      -a03ZeroModeMainKernel G N₁ N₂ a b α (-s) := by
  have hm := a03EtaMainFunction_reflection_of_small_shifts N₁ N₂ a b hα (-s)
  simp only [neg_neg] at hm
  unfold a03ZeroModeMainKernel
  rw [←hm,hEven]
  simp only [div_neg,neg_mul,neg_neg]

theorem a03ZeroModeMainContour_reverseNegative (G : ℂ → ℂ)
    (hEven : ∀ z, G (-z)=G z) (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    {α : MomentShifts} (hα : ∀ j : Fin 4, ‖α j‖≤1/8) (c : ℝ) :
    verticalIntegral c (a03ZeroModeMainKernel G N₁ N₂ a b
      (a03ZeroModeReverseNegative α)) =
      -verticalIntegral (-c) (a03ZeroModeMainKernel G N₁ N₂ a b α) := by
  have he : a03ZeroModeMainKernel G N₁ N₂ a b (a03ZeroModeReverseNegative α) =
      (fun s => -a03ZeroModeMainKernel G N₁ N₂ a b α (-s)) := by
    funext s
    exact a03ZeroModeMainKernel_reverseNegative G hEven N₁ N₂ a b hα s
  rw [he]
  unfold verticalIntegral
  rw [integral_neg,mul_neg]
  congr 1
  exact a03ZeroMode_verticalIntegral_reflection c (a03ZeroModeMainKernel G N₁ N₂ a b α)

/-- At the actual four chamber labels, the paired source contours are the
difference of the original lines `c` and `-c`. -/
theorem a03ZeroModeMainContour_chamber_pair (m n : Bool) (G : ℂ → ℂ)
    (hEven : ∀ z, G (-z)=G z) (N₁ N₂ : ℕ) (a b : ℕ → ℂ)
    {α : MomentShifts} (hα : ∀ j : Fin 4, ‖α j‖≤1/8) (c : ℝ) :
    verticalIntegral c (a03ZeroModeMainKernel G N₁ N₂ a b
      (a03ZeroModeChamberShifts m n α))+
      verticalIntegral c (a03ZeroModeMainKernel G N₁ N₂ a b
        (a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts α 1))) =
    verticalIntegral c (a03ZeroModeMainKernel G N₁ N₂ a b
      (a03ZeroModeChamberShifts m n α))-
      verticalIntegral (-c) (a03ZeroModeMainKernel G N₁ N₂ a b
        (a03ZeroModeChamberShifts m n α)) := by
  rw [←a03ZeroMode_chamber_dual_partner,
    a03ZeroModeMainContour_reverseNegative G hEven N₁ N₂ a b
      (a03ZeroMode_chamber_norm_le m n hα)]
  rfl

/-- The actual source `s=0` arithmetic value in each chamber, proved from
the global prime-factor identity (9). -/
theorem a03ZeroModeMainContour_chamber_zero_value (m n : Bool)
    (N₁ N₂ : ℕ) (a b : ℕ → ℂ) {α : MomentShifts}
    (hα : ∀ j : Fin 4, ‖α j‖≤1/8) :
    a03ZeroModeContourPrefactor (a03ZeroModeChamberShifts m n α)*
      a03EtaMainFunction N₁ N₂ a b (a03ZeroModeChamberShifts m n α) 0 =
      a03CrossedArithmeticSum N₁ N₂ a b (a03ZeroModeChamberShifts m n α) :=
  a03EtaMainFunction_zero_eq_crossedArithmetic N₁ N₂ a b
    (a03ZeroMode_chamber_norm_le m n hα)

end
end Sechstmoment.Source
