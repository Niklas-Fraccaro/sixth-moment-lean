import Mathlib.Data.List.OfFn
import Sechstmoment.Certificate.Features
import Sechstmoment.Certificate.Kernels.Balanced.IntegerEvaluator
import Sechstmoment.Certificate.Kernels.Unbalanced.IntegerEvaluator

namespace Sechstmoment.Finite

def gramZero (x y : Feature) : ℤ :=
  match x.typ, y.typ with
  | .U, .U => d0 x.A y.B x.B y.A x.poly y.poly +
      d0 x.A y.A x.B y.B x.poly (reflect y.poly)
  | .V, .V => d0 x.A x.B y.A y.B x.poly y.poly
  | _, _ => 0

def gramMinus (x y : Feature) : ℤ :=
  match x.typ, y.typ with
  | .U, .V => dminus x.B y.A y.B x.A y.poly x.poly +
      dminus x.A y.A y.B x.B x.poly (reflect y.poly)
  | _, _ => 0

def pairs : List (Nat × Nat) := (List.range 178).flatMap fun i =>
  (List.range (178-i)).map fun j => (i,i+j)

def feature (i : Nat) : Feature := features[i]?.getD ⟨.U,0,0,[]⟩

def pairZero (ij : Nat × Nat) : ℤ :=
  (if ij.1 = ij.2 then 1 else 2) * gramZero (feature ij.1) (feature ij.2)

def pairMinus (ij : Nat × Nat) : ℤ :=
  (if ij.1 = ij.2 then 1 else 2) * gramMinus (feature ij.1) (feature ij.2)

def blockSize : Nat := 128
def blockCount : Nat := 125
def chunks {α : Type} (size : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | n+1, xs => xs.take size :: chunks size n (xs.drop size)

theorem chunks_flatten {α : Type} (size n : Nat) (xs : List α)
    (h : xs.length ≤ n*size) : (chunks size n xs).flatten = xs := by
  induction n generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    simp [chunks, hx]
  | succ n ih =>
    simp only [chunks, List.flatten_cons]
    rw [ih]
    · exact List.take_append_drop _ _
    · simp only [List.length_drop]
      have hm : (n+1)*size = n*size+size := by simp [Nat.add_mul]
      omega

def blocks := chunks blockSize blockCount pairs
def pairBlock (k : Nat) := blocks[k]?.getD []
def blockZero (k : Nat) : ℤ := sum ((pairBlock k).map pairZero)
def blockMinus (k : Nat) : ℤ := sum ((pairBlock k).map pairMinus)

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem pairs_length : pairs.length = 15931 := by decide +kernel
theorem pair_indices_valid : ∀ ij ∈ pairs, ij.1 ≤ ij.2 ∧ ij.2 < 178 := by
  have h : pairs.all (fun ij => decide (ij.1 ≤ ij.2 ∧ ij.2 < 178)) = true := by decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h
theorem blocks_cover_pairs : blocks.flatten = pairs := by
  apply chunks_flatten
  rw [pairs_length]
  decide

end Sechstmoment.Finite
