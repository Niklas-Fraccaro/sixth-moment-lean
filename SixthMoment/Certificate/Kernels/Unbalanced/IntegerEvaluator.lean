import Mathlib.Data.Int.Basic
import SixthMoment.Certificate.Exact.KernelEvaluators
import Std


namespace SixthMoment.Finite

def dminusDenominator : ℤ := 256 * factorial 13

structure MomentTerm where
  i : ℕ
  j : ℕ
  l : ℕ
  h : ℕ
  value : ℤ
  deriving DecidableEq, Repr

def momentTerms (k mask : ℕ) : List MomentTerm :=
  let fac : ℤ := factorial k * 2^(8-k) * (factorial 13 / factorial (k+5) : ℕ)
  (List.range (k/2+1)).flatMap fun l1 =>
    (List.range (k/2-l1+1)).flatMap fun l2 =>
      let l3 := k/2-l1-l2
      let e1 := 2*l1+1
      let e2 := 2*l2+1
      let e3 := 2*l3+1
      (List.range (if bit mask 0 then e1+1 else 1)).flatMap fun d1 =>
        (List.range (if bit mask 1 then e2+1 else 1)).flatMap fun d2 =>
          (List.range (if bit mask 2 then e3+1 else 1)).map fun d3 =>
            let h := k+5-d1-d2-d3
            ⟨d1,d2,d3,h,fac*(factorial (k+5) /
              (factorial d1*factorial d2*factorial d3*factorial h) : ℕ)⟩

def dminus (A B C D : ℕ) (p q : List ℤ) : ℤ :=
  if A+B+C ≤ D then 0 else
  let vals : List ℤ := [24*A,24*B,24*C]
  let H := sum vals - 24*D
  let t0 := (scale-H)/2
  let pq := polyMul (shifted p (-t0) 1) (shifted q t0 1)
  sum ((List.range 8).map fun mask =>
    let HH := H-sum ((List.range 3).map fun i => if bit mask i then coef vals i else 0)
    if HH ≤ 0 then 0 else
    let sign : ℤ := (-1)^((List.range 3).filter (bit mask)).length
    sum ((List.range 5).map fun k2 =>
      let k := 2*k2
      if coef pq k = 0 then 0 else
      sign * coef pq k * sum ((momentTerms k mask).map fun tr =>
        tr.value * (coef vals 0)^tr.i * (coef vals 1)^tr.j * (coef vals 2)^tr.l * HH^tr.h)))

end SixthMoment.Finite
