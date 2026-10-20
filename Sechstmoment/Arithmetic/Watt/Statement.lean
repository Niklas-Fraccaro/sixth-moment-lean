import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic
import Sechstmoment.Arithmetic.Kloosterman.Definitions

/-!
# Watt, Proposition 4.1 (printed page 201)

Source: N. Watt, *Kloosterman Sums and a Mean Value for Dirichlet Polynomials*,
Journal of Number Theory 53 (1995), 179-210, Proposition 4.1, p. 201.
DOI: https://doi.org/10.1006/jnth.1995.1086

## Comparison with the source

* `U` is the sum of the absolute values of the inner sums, over coprime positive
  integers `r,s` in the closed intervals `[R/2,R]` and `[S/2,S]`.
* `p` ranges over all positive integers coprime to `r`. The paper's modular
  inverse convention (p. 183) imposes this restriction implicitly; equation
  (3.5), p. 195, also identifies `p` as an integer coprime to `r`.
* `classicalKloostermanSum` uses the convention on p. 183: its first argument
  multiplies the inverse of the summation variable. The separate inverse of
  `r` in the first argument is taken modulo `p*s`, as in Proposition 4.1.
* The weights `alpha`, `beta`, `omega` are complex-valued and the family `f` is
  real-valued. Their support intervals and derivative bounds match the source.
  Since all scales are at least one, support allows the unrestricted integer
  sums over `h,k,l,p` in the paper to be written as finite positive ranges.
* `Q = R*S`, `X = sqrt (R/(H*K*L))*S*P`, the condition
  `max (H^2*K) L <= Q^2`, and all factors of `majorant` match p. 201,
  including the powers `-7/2`, `1+epsilon`, `1/2` and `1/4`.

The formal statement fixes nonnegative derivative-bound sequences `b,fbound`.
It then chooses `C,X0` before the scales, `delta`, the sign, and the weights.
Thus these witnesses may depend on `epsilon,b,fbound`, but not on those
subsequently quantified inputs; the bounds for `f` are uniform in `r,s`.
This makes explicit the usual uniform reading of the paper's Vinogradov
notation and its sufficiently-large-`X` condition. The proof on p. 203 uses
a fixed threshold from Lemma 3.2, independent of the weights and scales.

We require the weights to be globally infinitely differentiable, with
topological support in the specified closed intervals. This is a restriction
of the allowed inputs, not an extension of the estimate to less regular
weights. Under the uniform reading above, Proposition 4.1 implies this
formulation; no converse or literal equivalence is asserted here.

`Watt41` is a proposition definition, not an axiom declaration or a theorem
proved by an admission. The source comparison above is mathematical
documentation, not a Lean proof of the external proposition. This file does
not identify the input with the different six-variable `WeightedWattBound`.
-/

namespace DivisorProof
open Real Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section

/-- Watt's convention (p. 183): `m` multiplies the inverse. -/
def classicalKloostermanSum (m n : ℤ) (c : ℕ) : ℂ :=
  kloostermanSum c n m

theorem classicalKloostermanSum_eq (m n : ℤ) (c : ℕ) :
    classicalKloostermanSum m n c =
      ∑ d ∈ (range c).filter (fun d => d.Coprime c),
        ePhase (((m : ℝ)*inverseRepresentative d c+(n : ℝ)*d)/(c : ℝ)) := by
  unfold classicalKloostermanSum kloostermanSum
  apply sum_congr rfl
  intro d _
  congr 1
  ring

namespace Watt41

structure Scales where
  H : ℝ
  K : ℝ
  L : ℝ
  P : ℝ
  R : ℝ
  S : ℝ

def Scales.Q (q : Scales) : ℝ := q.R*q.S
def Scales.X (q : Scales) : ℝ := Real.sqrt (q.R/(q.H*q.K*q.L))*q.S*q.P
def Scales.size (q : Scales) : Fin 6 → ℝ := ![q.H,q.K,q.L,q.P,q.R,q.S]

/-- Positive integers at most the scale. Support hypotheses supply lower ends. -/
def positiveRange (A : ℝ) : Finset ℕ := Icc 1 ⌊A⌋₊

/-- The exact half-open-at-zero, closed-at-both-dyadic-ends integer range. -/
def dyadicRange (A : ℝ) : Finset ℕ :=
  (positiveRange A).filter (fun n => A/2 ≤ (n : ℝ))

theorem mem_positiveRange {n : ℕ} {A : ℝ} :
    n ∈ positiveRange A ↔ 1 ≤ n ∧ (n : ℝ) ≤ A := by
  unfold positiveRange
  rw [Finset.mem_Icc]
  constructor
  · rintro ⟨hn, hA⟩
    have hA0 : 0 ≤ A := by
      by_contra h
      have : ⌊A⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact ⟨hn, (Nat.le_floor_iff hA0).mp hA⟩
  · rintro ⟨hn, hA⟩
    exact ⟨hn, (Nat.le_floor_iff ((Nat.cast_nonneg n).trans hA)).mpr hA⟩

theorem mem_dyadicRange {n : ℕ} {A : ℝ} :
    n ∈ dyadicRange A ↔ 1 ≤ n ∧ A/2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ A := by
  simp only [dyadicRange, mem_filter, mem_positiveRange]
  tauto

def pairRange (q : Scales) : Finset (ℕ × ℕ) :=
  ((dyadicRange q.R).product (dyadicRange q.S)).filter
    (fun rs => rs.1.Coprime rs.2)

structure WeightData (b fbound : ℕ → ℝ) (q : Scales) (δ : ℝ)
    (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℝ) : Prop where
  alpha_smooth : ContDiff ℝ ∞ α
  beta_smooth : ContDiff ℝ ∞ β
  omega_smooth : ContDiff ℝ ∞ w
  alpha_support : tsupport α ⊆ Icc (q.H/2) q.H
  beta_support : tsupport β ⊆ Icc (q.K/2) q.K
  omega_support : tsupport w ⊆ Icc (q.L/2) q.L
  alpha_derivatives : ∀ j x, 0 < x →
    ‖iteratedDeriv j α x‖ ≤ b j*(δ*x)^(-(j : ℝ))
  beta_derivatives : ∀ j x, 0 < x →
    ‖iteratedDeriv j β x‖ ≤ b j*(δ*x)^(-(j : ℝ))
  omega_derivatives : ∀ j x, 0 < x →
    ‖iteratedDeriv j w x‖ ≤ b j*(δ*x)^(-(j : ℝ))
  f_smooth : ∀ rs ∈ pairRange q, ContDiff ℝ ∞ (f rs.1 rs.2)
  f_support : ∀ rs ∈ pairRange q, tsupport (f rs.1 rs.2) ⊆ Icc (q.P/2) q.P
  f_derivatives : ∀ rs ∈ pairRange q, ∀ j x, 0 < x →
    ‖iteratedDeriv j (f rs.1 rs.2) x‖ ≤ fbound j*x^(-(j : ℝ))

/-- The inner sum for one outer coprime pair. -/
def innerSum (q : Scales) (σ : ℤ) (α β w : ℝ → ℂ)
    (f : ℕ → ℕ → ℝ → ℝ) (r s : ℕ) : ℂ :=
    ∑ h ∈ positiveRange q.H, ∑ k ∈ positiveRange q.K,
      ∑ l ∈ positiveRange q.L,
        α h*β k*w l*
        ∑ p ∈ (positiveRange q.P).filter (fun p => p.Coprime r),
          (f r s p : ℂ)*classicalKloostermanSum
            ((h : ℤ)*k*inverseRepresentative r (p*s)) (σ*l) (p*s)

/-- The quantity U in Proposition 4.1. All sums are finite by support. -/
def U (q : Scales) (σ : ℤ) (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℝ) : ℝ :=
  ∑ rs ∈ pairRange q, ‖innerSum q σ α β w f rs.1 rs.2‖

def majorant (q : Scales) (δ ε : ℝ) : ℝ :=
  δ^(-7/2 : ℝ)*q.H*q.K*q.L*(q.Q*q.X)^(1+ε)*
    ((1+q.H*q.K/q.Q)*(1+q.L/q.Q))^(1/2 : ℝ)*
    (1+q.H^2*q.K*q.L*q.X^2/q.Q^4)^(1/4 : ℝ)

theorem coprime_modulus {r s p : ℕ} (hrs : r.Coprime s) (hpr : p.Coprime r) :
    r.Coprime (p*s) := hpr.symm.mul_right hrs

theorem U_nonneg (q : Scales) (σ : ℤ) (α β w : ℝ → ℂ)
    (f : ℕ → ℕ → ℝ → ℝ) : 0 ≤ U q σ α β w f := by
  unfold U
  exact sum_nonneg (fun _ _ => norm_nonneg _)

end Watt41

/-- Globally smooth formulation of Watt's Proposition 4.1 (p. 201), with
uniform derivative bounds and the large-X threshold made explicit.
See the module documentation for the source comparison. -/
def Watt41 : Prop :=
  ∀ ε : ℝ, 0 < ε →
  ∀ b : ℕ → ℝ, (∀ j, 0 ≤ b j) →
  ∀ fbound : ℕ → ℝ, (∀ j, 0 ≤ fbound j) →
    ∃ C X₀ : ℝ, 0 ≤ C ∧ 1 ≤ X₀ ∧
      ∀ (q : Watt41.Scales) (δ : ℝ) (σ : ℤ)
        (α β w : ℝ → ℂ) (f : ℕ → ℕ → ℝ → ℝ),
        (∀ i, 1 ≤ q.size i) → 0 < δ → (σ = -1 ∨ σ = 1) →
        Watt41.WeightData b fbound q δ α β w f →
        max (q.H^2*q.K) q.L ≤ q.Q^2 → X₀ ≤ q.X →
        Watt41.U q σ α β w f ≤ C*Watt41.majorant q δ ε

end
end DivisorProof
