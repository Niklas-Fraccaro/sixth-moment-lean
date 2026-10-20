import SixthMoment.Numerator.U.ZeroModes.Ratio.ContourBounds


namespace SixthMoment.Source
open Complex
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioSideSwap (α : MomentShifts) : MomentShifts :=
  ![α 2,α 3,α 0,α 1]

theorem a03ZeroModeRatioSideSwap_small {ε : ℝ} {α : MomentShifts}
    (hα : ∀ j : Fin 4,‖α j‖≤ε/8) :
    ∀ j : Fin 4,‖a03ZeroModeRatioSideSwap α j‖≤ε/8 := by
  intro j
  fin_cases j <;> simpa [a03ZeroModeRatioSideSwap] using hα _

@[simp] theorem a03ZeroModeRatioRoot_sideSwap_zero (α : MomentShifts) :
    a03ZeroModeRatioRoot (a03ZeroModeRatioSideSwap α) 0=a03ZeroModeRatioRoot α 1 := by
  simp [a03ZeroModeRatioRoot,a03ZeroModeRatioSideSwap]

@[simp] theorem a03ZeroModeRatioRoot_sideSwap_one (α : MomentShifts) :
    a03ZeroModeRatioRoot (a03ZeroModeRatioSideSwap α) 1=a03ZeroModeRatioRoot α 0 := by
  simp [a03ZeroModeRatioRoot,a03ZeroModeRatioSideSwap]

theorem a03ZeroModeRatioSideSwap_roots_nonzero {α : MomentShifts}
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) :
    ∀ j : Fin 2,a03ZeroModeRatioRoot (a03ZeroModeRatioSideSwap α) j≠0 := by
  intro j
  fin_cases j <;> simpa using hρ _

theorem a03ZeroModeRatioWeight_sideSwap (α : MomentShifts) (z : ℂ) :
    a03ZeroModeRatioWeight (a03ZeroModeRatioSideSwap α) z=a03ZeroModeRatioWeight α z := by
  unfold a03ZeroModeRatioWeight
  rw [a03ZeroModeRatioRoot_sideSwap_zero,a03ZeroModeRatioRoot_sideSwap_one]
  ring

theorem a03ZeroModeRatioRemovedDifference_sideSwap_zero (α : MomentShifts) (z : ℂ) :
    a03ZeroModeRatioRemovedDifference (a03ZeroModeRatioSideSwap α) 0 z=
      a03ZeroModeRatioRemovedDifference α 1 z := by
  simp [a03ZeroModeRatioRemovedDifference,a03ZeroModeRatioOtherRoot,
    a03ZeroModeRatioDifferenceArgument]

theorem a03ZeroModeRatioRemovedDifference_sideSwap_one (α : MomentShifts) (z : ℂ) :
    a03ZeroModeRatioRemovedDifference (a03ZeroModeRatioSideSwap α) 1 z=
      a03ZeroModeRatioRemovedDifference α 0 z := by
  simp [a03ZeroModeRatioRemovedDifference,a03ZeroModeRatioOtherRoot,
    a03ZeroModeRatioDifferenceArgument]

theorem a03ZeroModeRatioEulerArgument_sideSwap (α : MomentShifts) (u v : ℂ) :
    a03ZeroModeRatioEulerArgument (a03ZeroModeRatioSideSwap α) v u=
      a03ZeroModeRatioEulerArgument α u v := by
  simp [a03ZeroModeRatioEulerArgument,a03ZeroModeRatioSideSwap]
  ring

theorem a03ZeroModeRatioEtaPair_sideSwap (α : MomentShifts) (a b : ℕ) (u v s : ℂ) :
    a03ZeroModeRatioEtaPair (a03ZeroModeRatioSideSwap α) b a v u s=
      a03ZeroModeRatioEtaPair α a b u v s := by
  simp [a03ZeroModeRatioEtaPair,a03ZeroModeRatioSideSwap,mul_comm]

theorem a03ZeroModeRatioArithmeticNumerator_sideSwap (α : MomentShifts)
    (a b : ℕ) (u v s : ℂ) :
    a03ZeroModeRatioArithmeticNumerator (a03ZeroModeRatioSideSwap α) b a v u s=
      a03ZeroModeRatioArithmeticNumerator α a b u v s := by
  unfold a03ZeroModeRatioArithmeticNumerator a03ZeroModeRatioRemovedPair
  rw [a03ZeroModeRatioRemovedDifference_sideSwap_zero,
    a03ZeroModeRatioRemovedDifference_sideSwap_one,
    a03ZeroModeRatioEulerArgument_sideSwap,a03ZeroModeRatioEtaPair_sideSwap]
  ring

theorem a03ZeroModeRatioArithmeticKernel_sideSwap (α : MomentShifts)
    (a b : ℕ) (u v s : ℂ) :
    a03ZeroModeRatioArithmeticKernel (a03ZeroModeRatioSideSwap α) b a v u s=
      a03ZeroModeRatioArithmeticKernel α a b u v s := by
  unfold a03ZeroModeRatioArithmeticKernel
  rw [a03ZeroModeRatioArithmeticNumerator_sideSwap,mul_comm v u]

end
end SixthMoment.Source
