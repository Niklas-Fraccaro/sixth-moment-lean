import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Sechstmoment
noncomputable section

def exponentialDifference (A B : ℂ) (x : ℝ) : ℂ :=
  (Complex.exp (-A*(x:ℂ))-Complex.exp (-B*(x:ℂ)))/(B-A)

end
end Sechstmoment
