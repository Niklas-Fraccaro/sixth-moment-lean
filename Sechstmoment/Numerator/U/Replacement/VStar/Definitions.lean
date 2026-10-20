import Sechstmoment.Numerator.U.Replacement.DualErrorGaussian
import Sechstmoment.Numerator.U.Replacement.VStar.Contours
import Sechstmoment.Numerator.U.Separation.SmallContour.Grid

namespace Sechstmoment.Source
open Complex Real MeasureTheory
open scoped BigOperators
noncomputable section

def bblrVStarAFESummand (G : ℂ → ℂ) (α : MomentShifts) (t : ℝ)
    (n : Fin 4 → ℕ) : ℂ :=
  rectangularAFEOscillation t n*bblrVStar G (positiveQuadProduct n/t^2)/
    ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j)

def bblrVStarAFESum (G : ℂ → ℂ) (α : MomentShifts) (t : ℝ) : ℂ :=
  ∑' n : Fin 4 → ℕ, bblrVStarAFESummand G α t n

end
end Sechstmoment.Source

namespace Sechstmoment
open Complex Real Source MeasureTheory
open scoped BigOperators
noncomputable section

def rectangularVStarAFEMellinKernel (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4 → ℕ) (z : ℂ) : ℂ :=
  rectangularAFEOscillation t n*bblrVStarKernel G (positiveQuadProduct n/t^2) z/
    ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j)

def bblrGaussianVStarCoreSummand (c T : ℝ) (σ α : MomentShifts)
    (t R : ℝ) (n : Fin 4 → ℕ) : ℂ :=
  rectangularAFEOscillation t n*bblrGaussianVStarCore c T σ (positiveQuadProduct n) t R/
    ∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j)

def rectangularFiniteSmallVStarCore (c T : ℝ) (σ α : MomentShifts) (t X R : ℝ) : ℂ :=
  ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
    (rectangularAFESmoothWeight k n:ℂ)*bblrGaussianVStarCoreSummand c T σ α t R n

def rectangularVStarAFEIntegrand (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) (t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*
    (bblrVStarAFESum (polarPoleKiller T σ) (rawMomentShifts T σ) t+
      bblrDualLeadingMultiplier T σ (t/T)*
        bblrVStarAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) t)

def rectangularVStarAFEMoment (T : ℝ) (σ : MomentShifts) (f g Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, rectangularVStarAFEIntegrand T σ f g Φ t

def rectangularFiniteSmallVStarIntegrand (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) (X R t : ℝ) : ℂ :=
  rectangularMomentWeight T f g Φ t*
    (rectangularFiniteSmallVStarCore c T σ (rawMomentShifts T σ) t X R+
      bblrDualLeadingMultiplier T σ (t/T)*
        rectangularFiniteSmallVStarCore c T σ (bblrSixShifts (rawMomentShifts T σ) 1) t X R)

def rectangularFiniteSmallVStarMoment (c T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) (X R : ℝ) : ℂ :=
  ∫ t : ℝ, rectangularFiniteSmallVStarIntegrand c T σ f g Φ X R t

end
end Sechstmoment
