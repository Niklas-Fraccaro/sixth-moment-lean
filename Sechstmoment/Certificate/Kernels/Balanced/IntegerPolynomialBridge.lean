import Sechstmoment.Certificate.Exact.NumeratorIntegral
import Sechstmoment.Certificate.Kernels.Balanced.IntegerNormalization

namespace Sechstmoment
open scoped BigOperators
open _root_.Sechstmoment.Finite

noncomputable def realPoly4 (p : List Int) (x : ℝ) : ℝ :=
  evalDegreeFour (fun k => (coef p k.val : ℝ)) x

def integerPoly4 (p : List Int) (x : Int) : Int :=
  Finite.sum ((List.range 5).map fun k => coef p k*x^k)

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem shifted_integer_polynomial (p : List Int) (delta sign x : Int) :
    (integerPoly4 (shifted p delta sign) x : ℝ)/(Finite.scale : ℝ)^4 =
      realPoly4 p (((delta : ℝ)+(sign : ℝ)*(x : ℝ))/(Finite.scale : ℝ)) := by
  norm_num [integerPoly4, shifted, realPoly4, evalDegreeFour,
    Finite.sum, coef, List.range_succ, Fin.sum_univ_succ,
    Finite.choose, Finite.factorial, Finite.scale, Finite.base]
  ring

end Sechstmoment
