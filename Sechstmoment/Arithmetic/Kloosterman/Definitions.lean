import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Basic

namespace DivisorProof
open Finset
open scoped BigOperators
noncomputable section

def inverseRepresentative (r c : ℕ) : ℕ := ((r : ZMod c)⁻¹).val

def ePhase (t : ℝ) : ℂ := Complex.exp (2*(Real.pi : ℂ)*Complex.I*(t : ℂ))

def kloostermanSum (c : ℕ) (u v : ℤ) : ℂ :=
  ∑ x ∈ (range c).filter (fun x => x.Coprime c),
    ePhase (((u:ℝ)*x+(v:ℝ)*inverseRepresentative x c)/(c:ℝ))

end
end DivisorProof
