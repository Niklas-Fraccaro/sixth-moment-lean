import SixthMoment.Arithmetic.QuadraticDivisor.Reduction.WattApplication
import SixthMoment.Arithmetic.Watt.Reduction

namespace SixthMoment.Source
noncomputable section

theorem separatedQuadraticInput_of_watt41 (hWatt : DivisorProof.Watt41) :
    SeparatedQuadraticInput :=
  DivisorProof.separatedDivisorBound_of_watt
    (DivisorProof.weightedWattBound_of_watt41 hWatt)

end
end SixthMoment.Source
