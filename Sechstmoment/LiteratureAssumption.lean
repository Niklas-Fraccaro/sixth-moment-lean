import Sechstmoment.Arithmetic.Watt.Statement
import Sechstmoment.Statement
import Sechstmoment.Zeta.AFE.Four.Specification


namespace Sechstmoment
noncomputable section

def LiteratureInputs : Prop := DivisorProof.Watt41

def LiteratureRelativeGoal : Prop := DivisorProof.Watt41 → FullGoal

theorem literatureRelativeGoal_iff :
    LiteratureRelativeGoal ↔ (LiteratureInputs → FullGoal) := Iff.rfl

end
end Sechstmoment
