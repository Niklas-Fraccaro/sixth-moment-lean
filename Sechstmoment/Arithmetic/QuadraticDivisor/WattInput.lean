import Sechstmoment.Arithmetic.QuadraticDivisor.Reduction.WattApplication
import Sechstmoment.Arithmetic.Watt.Reduction

namespace Sechstmoment.Source
noncomputable section

theorem separatedQuadraticInput_of_watt41 (hWatt : DivisorProof.Watt41) :
    SeparatedQuadraticInput :=
  DivisorProof.separatedDivisorBound_of_watt
    (DivisorProof.weightedWattBound_of_watt41 hWatt)

end
end Sechstmoment.Source
