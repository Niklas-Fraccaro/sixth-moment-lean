import Sechstmoment.Arithmetic.QuadraticDivisor.Reduction.WattApplication
import Sechstmoment.Arithmetic.Watt.Reduction

/-! The exact Watt proposition supplies the only divisor estimate consumed
by the sixth-moment proof. All source definitions are reused directly. -/
namespace Sechstmoment.Source
noncomputable section

theorem separatedQuadraticInput_of_watt41 (hWatt : DivisorProof.Watt41) :
    SeparatedQuadraticInput :=
  DivisorProof.separatedDivisorBound_of_watt
    (DivisorProof.weightedWattBound_of_watt41 hWatt)

end
end Sechstmoment.Source
