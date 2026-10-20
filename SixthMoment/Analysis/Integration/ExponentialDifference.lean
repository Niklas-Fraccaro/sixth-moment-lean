import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace SixthMoment
noncomputable section

def exponentialDifference (A B : ℂ) (x : ℝ) : ℂ :=
  (Complex.exp (-A*(x:ℂ))-Complex.exp (-B*(x:ℂ)))/(B-A)

end
end SixthMoment
