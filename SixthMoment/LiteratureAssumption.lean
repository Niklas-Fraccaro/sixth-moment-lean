import SixthMoment.Arithmetic.Watt.Statement
import SixthMoment.Statement
import SixthMoment.Zeta.AFE.Four.Specification


namespace SixthMoment
noncomputable section

def LiteratureInputs : Prop := DivisorProof.Watt41

def LiteratureRelativeGoal : Prop := DivisorProof.Watt41 → FullGoal

theorem literatureRelativeGoal_iff :
    LiteratureRelativeGoal ↔ (LiteratureInputs → FullGoal) := Iff.rfl

end
end SixthMoment
