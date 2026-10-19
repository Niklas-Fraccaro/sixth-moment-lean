import Sechstmoment.Arithmetic.Watt.Statement
import Sechstmoment.Statement
import Sechstmoment.Zeta.AFE.Four.Specification

/-! The original mathematical goal from the single remaining literature input.
The V limits needed by the certificate are proved internally. This does not
assert the stronger general sharp-endpoint DP contract. -/

namespace Sechstmoment
noncomputable section

/-- The sole external analytic premise, Watt Proposition 4.1. -/
def LiteratureInputs : Prop := DivisorProof.Watt41

/-- The original conclusion, with no additional moment or limit premise. -/
def LiteratureRelativeGoal : Prop := DivisorProof.Watt41 → FullGoal

theorem literatureRelativeGoal_iff :
    LiteratureRelativeGoal ↔ (LiteratureInputs → FullGoal) := Iff.rfl

end
end Sechstmoment
