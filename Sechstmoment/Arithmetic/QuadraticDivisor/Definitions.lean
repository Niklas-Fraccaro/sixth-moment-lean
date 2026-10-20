import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Sechstmoment.Analysis.Profiles.Classes
import Std


namespace Sechstmoment.Source
open Complex MeasureTheory Set Polynomial Filter Asymptotics
open Classical
open scoped BigOperators Topology

noncomputable section

structure QuadraticScales where
  A : ℝ
  B : ℝ
  M₁ : ℝ
  M₂ : ℝ
  N₁ : ℝ
  N₂ : ℝ
  H : ℝ

def QuadraticScales.M (q : QuadraticScales) : ℝ := q.M₁*q.M₂
def QuadraticScales.N (q : QuadraticScales) : ℝ := q.N₁*q.N₂
def QuadraticScales.mass (q : QuadraticScales) : ℝ := q.A*q.B*q.M*q.N

def QuadraticScales.size (q : QuadraticScales) : Fin 7 → ℝ :=
  ![q.A, q.B, q.M₁, q.M₂, q.N₁, q.N₂, q.H]

def quadraticIndexSet (q : QuadraticScales) : Finset (Fin 7 → ℕ) :=
  Fintype.piFinset fun j => Finset.Icc 1 ⌊2*q.size j⌋₊

def signedQuadraticRelation (positive : Bool) (n : Fin 7 → ℕ) : Prop :=
  (n 0 : ℤ)*n 2*n 3-(n 1 : ℤ)*n 4*n 5 =
    (if positive then (n 6 : ℤ) else -(n 6 : ℤ))

def quadraticSummand (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) (n : Fin 7 → ℕ) : ℂ :=
  α (n 0)*β (n 1)*(W 0 (n 6/q.H) : ℂ)*
    (W 1 (n 2/q.M₁) : ℂ)*(W 2 (n 3/q.M₂) : ℂ)*
    (W 3 (n 4/q.N₁) : ℂ)*(W 4 (n 5/q.N₂) : ℂ)

def signedQuadraticSum (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) : ℂ :=
  ∑ n ∈ quadraticIndexSet q,
    if signedQuadraticRelation positive n then quadraticSummand q α β W n else 0

def quadraticMainIndexSet (q : QuadraticScales) : Finset (Fin 5 → ℕ) :=
  Fintype.piFinset fun j => Finset.Icc 1
    ⌊2*(![q.A, q.B, q.M₁, q.N₁, q.H] : Fin 5 → ℝ) j⌋₊

def quadraticZeroModeSummand (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) (n : Fin 5 → ℕ) : ℂ :=
  let d : ℝ := Nat.gcd (n 0*n 2) (n 1*n 3)
  α (n 0)*β (n 1)*(W 0 (d*n 4/q.H) : ℂ)*
    (W 1 (n 2/q.M₁) : ℂ)*(W 3 (n 3/q.N₁) : ℂ)*
    ∫ x : ℝ in Ioi 0, (W 2 (n 1*n 3*x/(d*q.M₂)) : ℂ)*
      (W 4 (n 0*n 2*x/(d*q.N₂)) : ℂ)

def quadraticZeroMode (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) : ℂ :=
  ∑ n ∈ quadraticMainIndexSet q, quadraticZeroModeSummand q α β W n

def signedQuadraticDiscrepancy (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) : ℂ :=
  signedQuadraticSum positive q α β W - quadraticZeroMode q α β W

def orientedQuadraticMajorant (q : QuadraticScales) : ℝ :=
  (q.mass*q.H^2)^(1/4 : ℝ)*
    (2*q.A*q.B + q.H^(1/4 : ℝ)*
      (q.A^(3/8 : ℝ)*q.B^(1/8 : ℝ)+(q.A*q.B)^(1/4 : ℝ))*
      q.mass^(1/8 : ℝ))

def QuadraticAdmissible (ε δ K : ℝ) (bounds : ℕ → ℝ)
    (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) : Prop :=
  (∀ j, 1 ≤ q.size j) ∧
  q.M₁ ≤ q.M₂*q.mass^ε ∧ q.N₁ ≤ q.N₂*q.mass^ε ∧
  q.H ≤ K*(q.A*q.B)^(1/2+ε) ∧
  (q.A*q.B)^δ ≤ K*q.M*q.N ∧
  q.A*q.M ≤ K*q.B*q.N ∧ q.B*q.N ≤ K*q.A*q.M ∧
  q.B*q.N₁ ≤ q.A*q.M₁ ∧
  (∀ n : ℕ, (n : ℝ) ∉ Icc q.A (2*q.A) → α n = 0) ∧
  (∀ n : ℕ, (n : ℝ) ∉ Icc q.B (2*q.B) → β n = 0) ∧
  (∀ n : ℕ, ‖α n‖ ≤ K*q.A^ε) ∧
  (∀ n : ℕ, ‖β n‖ ≤ K*q.B^ε) ∧
  (∀ i, SmoothDyadicWeight (W i)) ∧
  (∀ j : ℕ, ∀ i : Fin 5, ∀ x : ℝ,
    ‖iteratedDeriv j (W i) x‖ ≤ bounds j*q.mass^ε)

end
end Sechstmoment.Source
