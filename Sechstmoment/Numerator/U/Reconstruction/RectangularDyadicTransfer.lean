import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Sechstmoment.Arithmetic.QuadraticDivisor.Estimates.BlockTransfer
import Sechstmoment.Arithmetic.QuadraticDivisor.Estimates.Exponents

/-!
Dyadic summation of primitive, uniformly bounded reconstructed source errors.
The input is the finer divisor-sum estimate, not the desired moment asymptotic.
-/

namespace Sechstmoment

open Filter Asymptotics
open scoped Topology BigOperators

/-- The small source exponent is chosen after the rectangular margin is fixed. -/
theorem rectangular_source_epsilon_exists {a b : ℝ} (hab : a ≤ b)
    (h : 3*a+5*b < 2) :
    ∃ ε : ℝ, 0 < ε ∧ 3*ε/2 ≤ rectangularSlack a b ∧
      9*ε/4 ≤ rectangularSlack a b := by
  obtain ⟨hd, _, _⟩ := rectangular_slack_bounds hab h
  refine ⟨rectangularSlack a b / 3, by positivity, ?_, ?_⟩ <;> linarith

/-- Logarithmically many primitive blocks yield a sublinear reconstructed sum. -/
theorem rectangular_primitive_blocks_isLittleO {ι : Type*} {a b C K L ε : ℝ}
    (hab : a ≤ b) (h : 3*a+5*b < 2) (hC : 0 ≤ C) (hK : 0 < K) (hL : 0 ≤ L)
    (hε₁ : 3*ε/2 ≤ rectangularSlack a b) (hε₂ : 9*ε/4 ≤ rectangularSlack a b)
    {N : ℝ} (hN : 0 ≤ N) (n : ℕ) (s : ℝ → Finset ι)
    (A B X H : ι → ℝ → ℝ) (E : ι → ℝ → ℂ)
    (hcard : ∀ᶠ T in atTop, ((s T).card : ℝ) ≤ N*(Real.log T)^n)
    (hprimitive : ∀ᶠ T in atTop, ∀ i ∈ s T,
      0 < A i T ∧ 0 < B i T ∧ 0 < X i T ∧ 0 < H i T ∧
      A i T ≤ T^a ∧ B i T ≤ T^b ∧ X i T ≤ L*T^(1+ε) ∧
      H i T ≤ (K*T^ε)*(A i T*B i T)^(1/2:ℝ)*X i T/T ∧
      ‖E i T‖ ≤ (C*T^ε)*rectangularQuadraticMajorant (A i T) (B i T) (X i T) (H i T)) :
    (fun T => ∑ i ∈ s T,
      ((T/((A i T*B i T)^(1/2:ℝ)*X i T) : ℝ) : ℂ)*E i T) =o[atTop]
        (fun T : ℝ => T) := by
  let D := C*K^(1/2:ℝ)+C*K^(3/4:ℝ)*L^(1/2:ℝ)
  have hd : 0 ≤ D := by dsimp [D]; positivity
  apply rectangular_finset_sum_isLittleO hab h hN hd n s
    (fun i T => ((T/((A i T*B i T)^(1/2:ℝ)*X i T) : ℝ) : ℂ)*E i T) hcard
  filter_upwards [hprimitive, eventually_ge_atTop (1:ℝ)] with T hp hT
  intro i hi
  obtain ⟨ha, hb, hx, hh, hea, heb, hex, heh, he⟩ := hp i hi
  have hbound := rectangular_block_error_bound (E i T) hT ha hb hx hh hC hK hL hab hea heb hex heh he
  have hpow₁ : T^(1/2+a+b+3*ε/2) ≤ T^rectangularFirstExponent a b (rectangularSlack a b) :=
    Real.rpow_le_rpow_of_exponent_le hT (by dsimp [rectangularFirstExponent]; linarith)
  have hpow₂ : T^(3/4+3*a/8+5*b/8+9*ε/4) ≤ T^rectangularSecondExponent a b (rectangularSlack a b) :=
    Real.rpow_le_rpow_of_exponent_le hT (by dsimp [rectangularSecondExponent]; linarith)
  calc
    _ ≤ (C*K^(1/2:ℝ))*T^rectangularFirstExponent a b (rectangularSlack a b) +
      (C*K^(3/4:ℝ)*L^(1/2:ℝ))*T^rectangularSecondExponent a b (rectangularSlack a b) :=
        hbound.trans (add_le_add (mul_le_mul_of_nonneg_left hpow₁ (by positivity))
          (mul_le_mul_of_nonneg_left hpow₂ (by positivity)))
    _ ≤ D*T^rectangularFirstExponent a b (rectangularSlack a b) +
      D*T^rectangularSecondExponent a b (rectangularSlack a b) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [D]
        have : 0 ≤ C*K^(3/4:ℝ)*L^(1/2:ℝ) := by positivity
        linarith
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [D]
        have : 0 ≤ C*K^(1/2:ℝ) := by positivity
        linarith
    _ = _ := by ring

/-- A literal finite Cartesian set of dyadic exponent indices. -/
noncomputable def rectangularDyadicIndices (d n : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun _ => Finset.range n

/-- The number of independently chosen dyadic scales is a fixed power of their depth. -/
theorem rectangular_dyadic_card (d n : ℕ) :
    (rectangularDyadicIndices d n).card = n^d := by
  simp [rectangularDyadicIndices, Fintype.card_piFinset]

/-- The cardinality loss of a literal dyadic grid is logarithmic. -/
theorem rectangular_dyadic_card_le (d n : ℕ) {T C : ℝ}
    (_hT : 1 ≤ T) (_hC : 0 ≤ C) (hn : (n:ℝ) ≤ C*Real.log T) :
    ((rectangularDyadicIndices d n).card : ℝ) ≤ C^d*(Real.log T)^d := by
  rw [rectangular_dyadic_card, Nat.cast_pow, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hn d

/-- Finite-block bounds are uniform in an arbitrary parameter set, rather than
merely pointwise in each fixed parameter. -/
theorem rectangular_uniform_sum_isLittleO {ι σ : Type*} {a b C D : ℝ}
    (hab : a ≤ b) (h : 3*a+5*b < 2) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (n : ℕ) (s : ℝ → Finset ι) (U : Set σ) (F : σ → ι → ℝ → ℂ)
    (hcard : ∀ᶠ T in atTop, ((s T).card : ℝ) ≤ C*(Real.log T)^n)
    (hblock : ∀ᶠ T in atTop, ∀ θ ∈ U, ∀ i ∈ s T,
      ‖F θ i T‖ ≤ D*(T^rectangularFirstExponent a b (rectangularSlack a b) +
        T^rectangularSecondExponent a b (rectangularSlack a b))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T in atTop, ∀ θ ∈ U,
      ‖∑ i ∈ s T, F θ i T‖ ≤ ε*T := by
  intro ε hε
  let B := fun T : ℝ => (C*D)*((Real.log T)^n*
    (T^rectangularFirstExponent a b (rectangularSlack a b) +
      T^rectangularSecondExponent a b (rectangularSlack a b)))
  have hb : B =o[atTop] (fun T : ℝ => T) :=
    (polylog_weighted_power_sum_isLittleO hab h n).const_mul_left (C*D)
  filter_upwards [hcard, hblock, hb.def hε, eventually_ge_atTop (1:ℝ)] with T hc hp he hT
  intro θ hθ
  have hpow : 0 ≤ T^rectangularFirstExponent a b (rectangularSlack a b) +
      T^rectangularSecondExponent a b (rectangularSlack a b) := by positivity
  have hnonneg : 0 ≤ B T := by
    dsimp [B]
    exact mul_nonneg (mul_nonneg hC hD)
      (mul_nonneg (pow_nonneg (Real.log_nonneg hT) _) hpow)
  calc
    _ ≤ ((s T).card:ℝ)*(D*(T^rectangularFirstExponent a b (rectangularSlack a b) +
      T^rectangularSecondExponent a b (rectangularSlack a b))) :=
        complex_finset_sum_norm_le_card_mul (s T) (fun i => F θ i T) (hp θ hθ)
    _ ≤ (C*(Real.log T)^n)*(D*(T^rectangularFirstExponent a b (rectangularSlack a b) +
      T^rectangularSecondExponent a b (rectangularSlack a b))) :=
        mul_le_mul_of_nonneg_right hc (mul_nonneg hD hpow)
    _ = B T := by dsimp [B]; ring
    _ ≤ _ := by simpa only [Real.norm_of_nonneg hnonneg, Real.norm_of_nonneg (by linarith : (0:ℝ) ≤ T)] using he

end Sechstmoment
