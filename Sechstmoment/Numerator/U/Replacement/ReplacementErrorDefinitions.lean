import Sechstmoment.Numerator.U.Reconstruction.FullAFEMoment
import Sechstmoment.Numerator.U.Replacement.VStar.Definitions
import Sechstmoment.Numerator.U.Separation.DualLeadingRegularity

/-! Literal separate unrestricted original-weight, dual-weight and dual-phase
replacement errors, and their finite small-contour counterparts. All four
AFE sums and both actual amplifier sums remain in these concrete functions. -/
namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

def rectangularOriginalWeightReplacementIntegrand (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*
    (bblrAFESum (polarPoleKiller T σ) (rawMomentShifts T σ) t-
      bblrVStarAFESum (polarPoleKiller T σ) (rawMomentShifts T σ) t)

def rectangularDualWeightReplacementIntegrand (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*bblrDualMultiplier t (rawMomentShifts T σ)*
    (bblrAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) t-
      bblrVStarAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) t)

def rectangularDualPhaseReplacementIntegrand (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*
    (bblrDualMultiplier t (rawMomentShifts T σ)-bblrDualLeadingMultiplier T σ (t/T))*
      bblrVStarAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) t

def rectangularOriginalWeightReplacementError (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ, rectangularOriginalWeightReplacementIntegrand T σ f g Φ t
def rectangularDualWeightReplacementError (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ, rectangularDualWeightReplacementIntegrand T σ f g Φ t
def rectangularDualPhaseReplacementError (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ, rectangularDualPhaseReplacementIntegrand T σ f g Φ t

def rectangularFiniteOriginalWeightReplacementIntegrand (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (X R t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*
    (rectangularFiniteSmallGaussianCore c T σ (rawMomentShifts T σ) t X R-
      rectangularFiniteSmallVStarCore c T σ (rawMomentShifts T σ) t X R)
def rectangularFiniteDualWeightReplacementIntegrand (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (X R t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*bblrDualMultiplier t (rawMomentShifts T σ)*
    (rectangularFiniteSmallGaussianCore c T σ (bblrSixShifts (rawMomentShifts T σ) 1) t X R-
      rectangularFiniteSmallVStarCore c T σ (bblrSixShifts (rawMomentShifts T σ) 1) t X R)
def rectangularFiniteDualPhaseReplacementIntegrand (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (X R t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*
    (bblrDualMultiplier t (rawMomentShifts T σ)-bblrDualLeadingMultiplier T σ (t/T))*
      rectangularFiniteSmallVStarCore c T σ (bblrSixShifts (rawMomentShifts T σ) 1) t X R

def rectangularFiniteOriginalWeightReplacementError (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (X R : ℝ) : ℂ :=
  ∫ t : ℝ, rectangularFiniteOriginalWeightReplacementIntegrand c T σ f g Φ X R t
def rectangularFiniteDualWeightReplacementError (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (X R : ℝ) : ℂ :=
  ∫ t : ℝ, rectangularFiniteDualWeightReplacementIntegrand c T σ f g Φ X R t
def rectangularFiniteDualPhaseReplacementError (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (X R : ℝ) : ℂ :=
  ∫ t : ℝ, rectangularFiniteDualPhaseReplacementIntegrand c T σ f g Φ X R t

def rectangularReplacementErrorPartIntegrand (p : Fin 3) (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) : ℝ→ℂ :=
  if p=0 then rectangularOriginalWeightReplacementIntegrand T σ f g Φ
  else if p=1 then rectangularDualWeightReplacementIntegrand T σ f g Φ
  else rectangularDualPhaseReplacementIntegrand T σ f g Φ
def rectangularFiniteReplacementErrorPartIntegrand (p : Fin 3) (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (X R : ℝ) : ℝ→ℂ :=
  if p=0 then rectangularFiniteOriginalWeightReplacementIntegrand c T σ f g Φ X R
  else if p=1 then rectangularFiniteDualWeightReplacementIntegrand c T σ f g Φ X R
  else rectangularFiniteDualPhaseReplacementIntegrand c T σ f g Φ X R
def rectangularReplacementErrorPart (p : Fin 3) (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) : ℂ := ∫ t : ℝ, rectangularReplacementErrorPartIntegrand p T σ f g Φ t
def rectangularFiniteReplacementErrorPart (p : Fin 3) (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (X R : ℝ) : ℂ :=
  ∫ t : ℝ, rectangularFiniteReplacementErrorPartIntegrand p c T σ f g Φ X R t

theorem rectangularReplacementIntegrands_sum (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (t : ℝ) :
    rectangularOriginalWeightReplacementIntegrand T σ f g Φ t+
      rectangularDualWeightReplacementIntegrand T σ f g Φ t+
        rectangularDualPhaseReplacementIntegrand T σ f g Φ t=
      rectangularFullAFEIntegrand T σ f g Φ t-rectangularVStarAFEIntegrand T σ f g Φ t := by
  unfold rectangularOriginalWeightReplacementIntegrand rectangularDualWeightReplacementIntegrand
    rectangularDualPhaseReplacementIntegrand rectangularFullAFEIntegrand rectangularVStarAFEIntegrand
  ring

theorem rectangularFiniteReplacementIntegrands_sum (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ) (X R t : ℝ) :
    rectangularFiniteOriginalWeightReplacementIntegrand c T σ f g Φ X R t+
      rectangularFiniteDualWeightReplacementIntegrand c T σ f g Φ X R t+
        rectangularFiniteDualPhaseReplacementIntegrand c T σ f g Φ X R t=
      rectangularFiniteSmallGaussianGridIntegrand c T σ f g Φ X R t-
        rectangularFiniteSmallVStarIntegrand c T σ f g Φ X R t := by
  unfold rectangularFiniteOriginalWeightReplacementIntegrand rectangularFiniteDualWeightReplacementIntegrand
    rectangularFiniteDualPhaseReplacementIntegrand rectangularFiniteSmallGaussianGridIntegrand
    rectangularFiniteSmallVStarIntegrand
  ring

theorem rectangularReplacementErrors_sum_eq_full_difference (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ→ℝ)
    (hfull : Integrable (rectangularFullAFEIntegrand T σ f g Φ))
    (hstar : Integrable (rectangularVStarAFEIntegrand T σ f g Φ))
    (h₀ : Integrable (rectangularOriginalWeightReplacementIntegrand T σ f g Φ))
    (h₁ : Integrable (rectangularDualWeightReplacementIntegrand T σ f g Φ))
    (h₂ : Integrable (rectangularDualPhaseReplacementIntegrand T σ f g Φ)) :
    rectangularOriginalWeightReplacementError T σ f g Φ+
      rectangularDualWeightReplacementError T σ f g Φ+
        rectangularDualPhaseReplacementError T σ f g Φ=
      rectangularFullAFEMoment T σ f g Φ-rectangularVStarAFEMoment T σ f g Φ := by
  unfold rectangularOriginalWeightReplacementError rectangularDualWeightReplacementError
    rectangularDualPhaseReplacementError rectangularFullAFEMoment rectangularVStarAFEMoment
  have h₀₁ : Integrable (fun t : ℝ => rectangularOriginalWeightReplacementIntegrand T σ f g Φ t+
      rectangularDualWeightReplacementIntegrand T σ f g Φ t) := h₀.add h₁
  rw [←integral_add h₀ h₁,←integral_add h₀₁ h₂,←integral_sub hfull hstar]
  apply integral_congr_ae
  filter_upwards [] with t
  exact rectangularReplacementIntegrands_sum T σ f g Φ t

end
end Sechstmoment
