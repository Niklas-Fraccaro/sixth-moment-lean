import Sechstmoment.Numerator.U.Replacement.DualErrorFourier
import Sechstmoment.Numerator.U.Replacement.VStar.Definitions

/-! Exact identification of the proved replacement kernels with differences
of the actual original/dual Gamma kernel and the literal VStar kernel.
Only positive real time is needed for the principal-power identity. -/

namespace Sechstmoment
open Complex Real Source
open scoped BigOperators
noncomputable section

theorem rectangularVStarAFEMellinKernel_eq_main_power
    (G : ℂ→ℂ) (α : MomentShifts) {t : ℝ} (ht : 0<t)
    (n : Fin 4→ℕ) (z : ℂ) :
    rectangularVStarAFEMellinKernel G α t n z=
      G z/z*(t/2:ℂ)^(2*z)*(Real.pi:ℂ)^(-2*z)*
        rectangularAFEOscillation t n/∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+z) := by
  have hx : (0:ℝ)<positiveQuadProduct n := by unfold positiveQuadProduct; positivity
  have hmain : (t/2:ℂ)^(2*z)*(Real.pi:ℂ)^(-2*z)*(positiveQuadProduct n:ℂ)^(-z)=
      (2*Real.pi:ℂ)^(-2*z)*(positiveQuadProduct n/t^2:ℂ)^(-z) := by
    simpa using bblr_main_positive_cpow_identity ht hx z
  unfold rectangularVStarAFEMellinKernel bblrVStarKernel
  push_cast
  calc
    _ = (G z/z*rectangularAFEOscillation t n)*
        ((2*Real.pi:ℂ)^(-2*z)*(positiveQuadProduct n/t^2:ℂ)^(-z))/
          ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j) := by ring
    _ = (G z/z*(t/2:ℂ)^(2*z)*(Real.pi:ℂ)^(-2*z)*rectangularAFEOscillation t n)*
        ((positiveQuadProduct n:ℂ)^(-z)/∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j)) := by
      rw [←hmain]
      ring
    _ = _ := by rw [rectangular_AFE_Mellin_powers]; ring

theorem rectangularWeightReplacementMellinKernel_eq_actual_sub_star
    (G : ℂ→ℂ) (α : MomentShifts) {t : ℝ} (ht : 0<t)
    (n : Fin 4→ℕ) (z : ℂ) :
    rectangularWeightReplacementMellinKernel G α t n z=
      rectangularAFEMellinKernel G α t n z-
        rectangularVStarAFEMellinKernel G α t n z := by
  rw [rectangularVStarAFEMellinKernel_eq_main_power G α ht]
  unfold rectangularWeightReplacementMellinKernel rectangularAFEMellinKernel
  ring

theorem rectangularDualReplacementMellinKernel_eq_actual_sub_leading_star
    (T : ℝ) (σ : MomentShifts) (G : ℂ→ℂ) (α : MomentShifts)
    {t : ℝ} (ht : 0<t) (n : Fin 4→ℕ) (z : ℂ) :
    rectangularDualReplacementMellinKernel T σ G α t n z=
      bblrDualMultiplier t (rawMomentShifts T σ)*rectangularAFEMellinKernel G α t n z-
        (t/(2*Real.pi):ℂ)^(-∑ j : Fin 4, rawMomentShifts T σ j)*
          rectangularVStarAFEMellinKernel G α t n z := by
  rw [rectangularVStarAFEMellinKernel_eq_main_power G α ht]
  unfold rectangularDualReplacementMellinKernel rectangularAFEMellinKernel
  ring

end
end Sechstmoment
