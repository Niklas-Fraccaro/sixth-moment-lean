import Sechstmoment.Certificate.Features

namespace Sechstmoment.Finite
structure NumeratorTerm where
  i : Nat
  j : Nat
  coefficient : Int
  deriving DecidableEq, Repr

def numeratorTerms0 : List NumeratorTerm := [
  ⟨2,1,8400⟩,
  ⟨2,2,-16800⟩,
  ⟨2,3,8400⟩,
  ⟨3,0,-2800⟩,
  ⟨3,2,8400⟩,
  ⟨3,3,-5600⟩
]

def numeratorTerms1 : List NumeratorTerm := [
  ⟨2,2,-2100⟩,
  ⟨2,3,4200⟩,
  ⟨2,4,-2100⟩,
  ⟨3,1,2800⟩,
  ⟨3,2,-4200⟩,
  ⟨3,4,1400⟩,
  ⟨4,0,-700⟩,
  ⟨4,2,2100⟩,
  ⟨4,3,-1400⟩
]

def numeratorTerms2 : List NumeratorTerm := [
  ⟨2,1,420⟩,
  ⟨2,2,-1260⟩,
  ⟨2,3,2100⟩,
  ⟨2,4,-2100⟩,
  ⟨2,5,840⟩,
  ⟨3,0,-140⟩,
  ⟨3,2,-700⟩,
  ⟨3,3,1400⟩,
  ⟨3,5,-560⟩,
  ⟨4,1,1400⟩,
  ⟨4,2,-2100⟩,
  ⟨4,4,700⟩,
  ⟨5,0,-280⟩,
  ⟨5,2,840⟩,
  ⟨5,3,-560⟩
]

def numeratorTerms3 : List NumeratorTerm := [
  ⟨2,2,-315⟩,
  ⟨2,3,1050⟩,
  ⟨2,4,-1575⟩,
  ⟨2,5,1260⟩,
  ⟨2,6,-420⟩,
  ⟨3,1,420⟩,
  ⟨3,2,-1050⟩,
  ⟨3,3,1400⟩,
  ⟨3,4,-1050⟩,
  ⟨3,6,280⟩,
  ⟨4,0,-105⟩,
  ⟨4,2,-525⟩,
  ⟨4,3,1050⟩,
  ⟨4,5,-420⟩,
  ⟨5,1,840⟩,
  ⟨5,2,-1260⟩,
  ⟨5,4,420⟩,
  ⟨6,0,-140⟩,
  ⟨6,2,420⟩,
  ⟨6,3,-280⟩
]

def numeratorTerms4 : List NumeratorTerm := [
  ⟨2,1,45⟩,
  ⟨2,2,-180⟩,
  ⟨2,3,525⟩,
  ⟨2,4,-1050⟩,
  ⟨2,5,1260⟩,
  ⟨2,6,-840⟩,
  ⟨2,7,240⟩,
  ⟨3,0,-15⟩,
  ⟨3,2,-315⟩,
  ⟨3,3,1050⟩,
  ⟨3,4,-1400⟩,
  ⟨3,5,840⟩,
  ⟨3,7,-160⟩,
  ⟨4,1,420⟩,
  ⟨4,2,-1050⟩,
  ⟨4,3,1400⟩,
  ⟨4,4,-1050⟩,
  ⟨4,6,280⟩,
  ⟨5,0,-84⟩,
  ⟨5,2,-420⟩,
  ⟨5,3,840⟩,
  ⟨5,5,-336⟩,
  ⟨6,1,560⟩,
  ⟨6,2,-840⟩,
  ⟨6,4,280⟩,
  ⟨7,0,-80⟩,
  ⟨7,2,240⟩,
  ⟨7,3,-160⟩
]

def numeratorTerms (r : Nat) : List NumeratorTerm :=
  match r with
  | 0 => numeratorTerms0
  | 1 => numeratorTerms1
  | 2 => numeratorTerms2
  | 3 => numeratorTerms3
  | 4 => numeratorTerms4
  | _ => []

def numeratorMonomialInteger (r A B : Nat) : Int :=
  sum ((numeratorTerms r).map fun tr =>
    tr.coefficient * (base : Int)^(10-tr.i-tr.j) * (A : Int)^tr.i * (B : Int)^tr.j)

def numeratorFeatureInteger (f : Feature) : Int :=
  let B := if f.typ = .U then f.B else base-f.B
  sum ((List.range 5).map fun r => coef f.poly r * numeratorMonomialInteger r f.A B)

def numeratorInteger : Int := sum (features.map numeratorFeatureInteger)
def numeratorDenominator : Int := 201600 * (base : Int)^10

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem numerator_integer_exact : numeratorInteger = 930568882094372558575943745133742918423060187361605230240287840764380552571003174603513856 := by decide +kernel
end Sechstmoment.Finite
