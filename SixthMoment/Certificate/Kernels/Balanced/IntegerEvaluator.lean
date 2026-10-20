import Mathlib.Data.Int.Basic
import SixthMoment.Analysis.Quadrature.IntegerWeights
import SixthMoment.Certificate.Exact.KernelEvaluators
import Std


namespace SixthMoment.Finite

def w6 (t a b c d : ℤ) : ℤ :=
  let lo := max 0 (t-b)
  let hi := min a t
  let ll := max 0 (t-d)
  let hh := min c t
  if hi ≤ lo ∨ hh ≤ ll then 0 else
    3*(hi^2-lo^2)*(hh-ll) +
      (max (hi-hh) 0)^3 - (max (hi+hh-t) 0)^3 -
      (max (lo-hh) 0)^3 + (max (lo+hh-t) 0)^3 -
      (max (hi-ll) 0)^3 + (max (hi+ll-t) 0)^3 +
      (max (lo-ll) 0)^3 - (max (lo+ll-t) 0)^3

def d0 (A B C D : ℕ) (p q : List ℤ) : ℤ :=
  let delta : ℤ := 12*((A : ℤ)+B-C-D)
  let pq := polyMul (shifted p delta (-1)) (shifted q (-delta) (-1))
  let cs := (List.range 5).map fun (k : ℕ) => 2*(315/(2*(k : ℤ)+1))*coef pq (2*k)
  let e := min (A+B) (C+D)
  let knots := sort (([0,e] ++ [A,B,C,D,A+C,A+D,B+C,B+D].filter (fun v => decide (0<v ∧ v<e))).eraseDups)
  let a : ℤ := 24*A
  let b : ℤ := 24*B
  let c : ℤ := 24*C
  let d : ℤ := 24*D
  let center := scale-a-b-c-d
  sum ((knots.zip knots.tail).map fun (left,right) =>
    24*((right : ℤ)-left)*sum ((List.range 13).map fun (j : ℕ) =>
      let t : ℤ := 24*left + 2*((right : ℤ)-left)*j
      let H := (center+2*t)/2
      let inner := cs.reverse.foldl (fun acc cc => acc*H^2+cc) 0 * H
      coef ncNumerators j * w6 t a b c d * inner))

def d0Denominator : ℤ := 6 * 315 * 63063000
end SixthMoment.Finite
