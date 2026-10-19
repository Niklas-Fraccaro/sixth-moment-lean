import Sechstmoment.Certificate.Kernels.Balanced.IntegerPolynomialBridge

namespace Sechstmoment
open _root_.Sechstmoment.Finite

def integerInner (p q : List Int) (delta H : Int) : Int :=
  let pq := polyMul (shifted p delta (-1)) (shifted q (-delta) (-1))
  let cs := (List.range 5).map fun (k : Nat) =>
    2*(315/(2*(k : Int)+1))*coef pq (2*k)
  cs.reverse.foldl (fun acc cc => acc*H^2+cc) 0 * H

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem integerInner_integral (p q : List Int) (delta H : Int) :
    (integerInner p q delta H : ℝ)/(315*(Finite.scale : ℝ)^9) =
      ∫ x in -((H : ℝ)/(Finite.scale : ℝ))..((H : ℝ)/(Finite.scale : ℝ)),
        realPoly4 p ((delta : ℝ)/(Finite.scale : ℝ)-x)*
          realPoly4 q (-(delta : ℝ)/(Finite.scale : ℝ)-x) := by
  unfold realPoly4
  simp only [neg_div]
  rw [denominator_inner_integral]
  norm_num [integerInner, polyMul, shifted, Finite.sum, coef, List.range_succ,
    Finite.choose, Finite.factorial, Finite.scale, Finite.base,
    innerCoefficient, productCoefficient, shiftedCoefficient,
    Fin.sum_univ_succ, Nat.choose]
  ring

end Sechstmoment
