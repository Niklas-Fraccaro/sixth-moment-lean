import Sechstmoment.Numerator.U.ZeroModes.PhysicalReplacement

/-! The literal linear gap character used in the two-sign cosine zero mode. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03LeadingLinearTensorRawKernel (Φ : ℝ→ℂ) (c : ℝ) (p : A03NearTensorData)
    (y : A03SixTensorSpace) : ℂ :=
  a03TensorMellinFactor p.α ((c:ℂ)+(p.v:ℂ)*I) y*
    a03GaussianLeadingFrequencyProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I)
      (-p.T*p.s*p.r*Real.exp (a03SixGapLinear y))

def a03LeadingLinearDualTensorRawKernel (Φ : ℝ→ℂ) (c : ℝ) (p : A03NearTensorData)
    (y : A03SixTensorSpace) : ℂ :=
  a03TensorMellinFactor p.α ((c:ℂ)+(p.v:ℂ)*I) y*
    a03GaussianDualLeadingFrequencyProfile Φ p.T p.σ p.α ((c:ℂ)+(p.v:ℂ)*I)
      (-p.T*p.s*p.r*Real.exp (a03SixGapLinear y))

def a03ZeroModeLinearKernel (dual : Bool) (Φ : ℝ→ℂ) (c : ℝ) :
    A03NearTensorData→A03SixTensorSpace→ℂ :=
  if dual then a03LeadingLinearDualTensorRawKernel Φ c else a03LeadingLinearTensorRawKernel Φ c

def a03ZeroModeLinearizationKernel (dual : Bool) (Φ : ℝ→ℂ) (c : ℝ)
    (p : A03NearTensorData) (y : A03SixTensorSpace) : ℂ :=
  a03ZeroModeLeadingKernel dual Φ c p y-a03ZeroModeLinearKernel dual Φ c p y

end
end Sechstmoment
