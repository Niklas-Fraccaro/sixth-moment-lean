import Sechstmoment.Arithmetic.QuadraticDivisor.Definitions
import Sechstmoment.Arithmetic.QuadraticDivisor.Parameters

/-! Internal divisor interface with separate input and output exponents.
The source factory may choose any positive admissibility exponent. Watt 4.1
supplies the displayed output estimate at the smaller input exponent below.
This is a proved intermediate contract, not an additional external assumption. -/
namespace Sechstmoment.Source
open scoped BigOperators
noncomputable section

def SeparatedQuadraticInput : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ K : ℝ, 1 ≤ K →
  ∀ bounds : ℕ → ℝ, (∀ j, 0 ≤ bounds j) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ),
      QuadraticAdmissible (DivisorProof.inputExponent ε δ) δ K bounds q α β W →
      ∀ positive : Bool, ‖signedQuadraticDiscrepancy positive q α β W‖ ≤
        C*((q.mass*q.H^2)^ε*orientedQuadraticMajorant q+q.mass^ε*q.H^2)

end
end Sechstmoment.Source
