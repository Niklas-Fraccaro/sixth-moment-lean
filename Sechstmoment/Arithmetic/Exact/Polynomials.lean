import Mathlib.Data.Int.Basic
import Std


namespace Sechstmoment.Finite

def factorial : ℕ → ℕ
  | 0 => 1
  | n+1 => (n+1) * factorial n

def choose (n k : ℕ) : ℤ :=
  if k ≤ n then (factorial n / (factorial k * factorial (n-k)) : ℕ) else 0

def sum (xs : List ℤ) : ℤ := xs.foldl (· + ·) 0
def coef (p : List ℤ) (k : ℕ) : ℤ := p[k]?.getD 0

def polyMul (p q : List ℤ) : List ℤ :=
  (List.range (p.length + q.length - 1)).map fun k =>
    sum ((List.range p.length).map fun r =>
      if r ≤ k then coef p r * coef q (k-r) else 0)

def insertSorted (v : ℕ) : List ℕ → List ℕ
  | [] => [v]
  | x::xs => if v ≤ x then v::x::xs else x::insertSorted v xs

def sort (xs : List ℕ) : List ℕ := xs.foldr insertSorted []

def reflect (p : List ℤ) : List ℤ := p.zipIdx.map fun (c,k) => c*(-1)^k

def bit (mask i : ℕ) : Bool := mask / 2^i % 2 == 1

end Sechstmoment.Finite
