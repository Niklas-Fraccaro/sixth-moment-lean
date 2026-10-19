import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Sechstmoment.Arithmetic.QuadraticDivisor.Reduction.Poisson
import Std

/-! ## Outer Cardinality -/

/-! Explicit outer-tuple counting for the finite Poisson truncation. -/
namespace DivisorProof
open MeasureTheory Set Finset
open scoped BigOperators
noncomputable section

/-- The actual five-variable outer index set contains at most `32 ABM₁N₁H` tuples. -/
theorem quadraticMainIndexSet_card_le (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j) :
    ((quadraticMainIndexSet q).card : ℝ) ≤ 32*q.A*q.B*q.M₁*q.N₁*q.H := by
  let sizes : Fin 5 → ℝ := ![q.A, q.B, q.M₁, q.N₁, q.H]
  have hs (j : Fin 5) : 0 ≤ sizes j := by
    fin_cases j
    · exact zero_le_one.trans (h 0)
    · exact zero_le_one.trans (h 1)
    · exact zero_le_one.trans (h 2)
    · exact zero_le_one.trans (h 4)
    · exact zero_le_one.trans (h 6)
  have hc : ((quadraticMainIndexSet q).card : ℝ) =
      ∏ j : Fin 5, (⌊2*sizes j⌋₊ : ℝ) := by
    simp only [quadraticMainIndexSet, Fintype.card_piFinset, Nat.card_Icc,
      Nat.add_sub_cancel, Nat.cast_prod]
    rfl
  rw [hc]
  calc _ ≤ ∏ j : Fin 5, 2*sizes j :=
      Finset.prod_le_prod₀ (fun _ _ => Nat.cast_nonneg _)
        (fun j _ => Nat.floor_le (mul_nonneg (by norm_num) (hs j)))
    _ = 32*q.A*q.B*q.M₁*q.N₁*q.H := by simp [sizes, Fin.prod_univ_succ]; ring

/-- The source hypotheses with `ρ ≤ 1/2` give the crude bound `H ≤ KQ`. -/
theorem shiftScale_le_mass (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    {K ρ : ℝ} (hK : 0 ≤ K) (hρ : ρ ≤ 1/2)
    (hH : q.H ≤ K*(q.A*q.B)^(1/2+ρ)) : q.H ≤ K*q.mass := by
  obtain ⟨hAB, hABQ⟩ := product_AB_le_mass q h
  have hp : (q.A*q.B)^(1/2+ρ) ≤ q.A*q.B := by
    calc _ ≤ (q.A*q.B)^(1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hAB (by linarith)
      _ = _ := Real.rpow_one _
  exact hH.trans ((mul_le_mul_of_nonneg_left hp hK).trans (mul_le_mul_of_nonneg_left hABQ hK))

/-- The precise `O_K(Q²)` counting bound used in §4.3. -/
theorem quadraticMainIndexSet_card_le_mass_sq (q : QuadraticScales)
    (h : ∀ j, 1 ≤ q.size j) {K : ℝ} (hH : q.H ≤ K*q.mass) :
    ((quadraticMainIndexSet q).card : ℝ) ≤ (32*K)*q.mass^2 := by
  have hH0 : 0 ≤ q.H := zero_le_one.trans (h 6)
  have hprod := (poisson_scale_bounds q h).2.2.2.2
  calc _ ≤ 32*q.A*q.B*q.M₁*q.N₁*q.H := quadraticMainIndexSet_card_le q h
    _ = 32*(q.A*q.B*q.M₁*q.N₁)*q.H := by ring
    _ ≤ 32*q.mass*(K*q.mass) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hprod (by norm_num)) hH hH0
        (mul_nonneg (by norm_num) (zero_le_one.trans (poisson_scale_bounds q h).1))
    _ = (32*K)*q.mass^2 := by ring

end
end DivisorProof


/-! ## Weight Shift -/

/-! Mean-value and factorization estimates underlying the shift removal (18). -/
namespace DivisorProof
open Set Finset
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 800000

/-- The mean-value estimate uses the actual first derivative of the weight. -/
theorem weight_lipschitz_bound {W : ℝ → ℝ} (hW : SmoothDyadicWeight W)
    {b : ℝ} (hder : ∀ x, ‖iteratedDeriv 1 W x‖ ≤ b) (x y : ℝ) :
    ‖W y-W x‖ ≤ b*‖y-x‖ := by
  apply (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hW.1.differentiable (by simp)).differentiableAt)
    (fun z _ => by simpa only [iteratedDeriv_one] using hder z) (mem_univ x) (mem_univ y)

/-- The pointwise shift-removal estimate, valid for either sign of the shift. -/
theorem weight_shift_bound {W : ℝ → ℝ} (hW : SmoothDyadicWeight W)
    {b : ℝ} (hder : ∀ x, ‖iteratedDeriv 1 W x‖ ≤ b)
    (u s : ℝ) {v : ℝ} (hv : 0 < v) :
    ‖W ((u-s)/v)-W (u/v)‖ ≤ b*|s|/v := by
  have h := weight_lipschitz_bound hW hder (u/v) ((u-s)/v)
  have heq : (u-s)/v-u/v = -s/v := by ring
  simpa only [heq, norm_div, norm_neg, Real.norm_eq_abs, abs_of_pos hv, mul_div_assoc] using h

/-- The normalized dyadic pointwise error is `O_K(H/(AM))`. -/
theorem dyadic_weight_shift_bound {W : ℝ → ℝ} (hW : SmoothDyadicWeight W)
    {b : ℝ} (hder : ∀ x, ‖iteratedDeriv 1 W x‖ ≤ b)
    {U V H K s : ℝ} (hU : 0 < U) (hV : 0 < V) (hH : 0 ≤ H) (_hK : 0 ≤ K)
    (hbalance : U ≤ K*V) (hshift : |s| ≤ 2*H) (u : ℝ) :
    ‖W ((u-s)/V)-W (u/V)‖ ≤ 2*b*K*H/U := by
  have hb : 0 ≤ b := (norm_nonneg _).trans (hder 0)
  apply (weight_shift_bound hW hder u s hV).trans
  apply (div_le_div_iff₀ hV hU).mpr
  calc (b*|s|)*U ≤ (b*(2*H))*(K*V) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hshift hb) hbalance hU.le (by positivity)
    _ = (2*b*K*H)*V := by ring

/-- Positive ordered ternary factorizations, as a literal finite set. -/
def tripleFactorizations (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.Icc 1 n) ×ˢ ((Finset.Icc 1 n) ×ˢ (Finset.Icc 1 n))).filter
    (fun t => t.1*t.2.1*t.2.2 = n)

theorem mem_tripleFactorizations {a b c n : ℕ} :
    (a, b, c) ∈ tripleFactorizations n ↔ 0 < a ∧ 0 < b ∧ 0 < c ∧ a*b*c = n := by
  constructor
  · intro ht
    obtain ⟨habc, heq⟩ := mem_filter.mp ht
    obtain ⟨ha, hbc⟩ := mem_product.mp habc
    obtain ⟨hb, hc⟩ := mem_product.mp hbc
    exact ⟨(Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp hb).1,
      (Finset.mem_Icc.mp hc).1, heq⟩
  · rintro ⟨ha, hb, hc, rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha, ?_⟩,
      mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hb, ?_⟩, Finset.mem_Icc.mpr ⟨hc, ?_⟩⟩⟩, rfl⟩
    · exact (le_mul_of_one_le_right (Nat.zero_le a) hb).trans
        (le_mul_of_one_le_right (Nat.zero_le (a*b)) hc)
    · exact (le_mul_of_one_le_left (Nat.zero_le b) ha).trans
        (le_mul_of_one_le_right (Nat.zero_le (a*b)) hc)
    · exact le_mul_of_one_le_left (Nat.zero_le c) (Nat.mul_pos ha hb)

/-- A ternary factorization is determined by two divisors of `n`. -/
theorem tripleFactorizations_card_le_divisor_sq (n : ℕ) (hn : n ≠ 0) :
    (tripleFactorizations n).card ≤ n.divisors.card^2 := by
  classical
  calc
    _ ≤ (n.divisors ×ˢ n.divisors).card := by
      apply card_le_card_of_injOn (fun t : ℕ × ℕ × ℕ => (t.1, t.2.1))
      · intro t ht
        have heq := (mem_filter.mp ht).2
        apply mem_product.mpr
        constructor
        · apply Nat.mem_divisors.mpr
          refine ⟨⟨t.2.1*t.2.2, ?_⟩, hn⟩
          simpa only [mul_assoc] using heq.symm
        · apply Nat.mem_divisors.mpr
          refine ⟨⟨t.1*t.2.2, ?_⟩, hn⟩
          calc n = t.1*t.2.1*t.2.2 := heq.symm
            _ = t.2.1*(t.1*t.2.2) := by ring
      · intro t ht t' ht' heq
        have ha : t.1 = t'.1 := congrArg (fun z : ℕ × ℕ => z.1) heq
        have hb : t.2.1 = t'.2.1 := congrArg (fun z : ℕ × ℕ => z.2) heq
        have htprod := (mem_filter.mp ht).2
        have ht'prod := (mem_filter.mp ht').2
        have hta := (Finset.mem_Icc.mp (mem_product.mp (mem_filter.mp ht).1).1).1
        have htb := (Finset.mem_Icc.mp (mem_product.mp (mem_product.mp (mem_filter.mp ht).1).2).1).1
        have hprod0 : t.1*t.2.1 ≠ 0 := mul_ne_zero (by omega) (by omega)
        rw [← ha, ← hb] at ht'prod
        exact Prod.ext ha (Prod.ext hb (mul_left_cancel₀ hprod0 (htprod.trans ht'prod.symm)))
    _ = n.divisors.card^2 := by simp [pow_two]

/-- The source's `τ₃(n) ≪ρ n^ρ` estimate is proved, rather than assumed. -/
theorem tripleFactorizations_subpower {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≠ 0 →
      ((tripleFactorizations n).card : ℝ) ≤ C*(n : ℝ)^ρ := by
  obtain ⟨C, hC, hc⟩ := divisor_count_sq_subpower hρ
  refine ⟨C, hC, fun n hn => ?_⟩
  have hcard : ((tripleFactorizations n).card : ℝ) ≤ (n.divisors.card : ℝ)^2 := by
    exact_mod_cast tripleFactorizations_card_le_divisor_sq n hn
  exact hcard.trans (hc n hn)

theorem tripleFactorizations_zero : tripleFactorizations 0 = ∅ := by
  simp [tripleFactorizations]

/-- The bound extends to zero because there are no positive factorizations of zero. -/
theorem tripleFactorizations_subpower_all {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ((tripleFactorizations n).card : ℝ) ≤ C*(n : ℝ)^ρ := by
  obtain ⟨C, hC, hc⟩ := tripleFactorizations_subpower hρ
  refine ⟨C, hC, fun n => ?_⟩
  by_cases hn : n = 0
  · subst n
    simp only [tripleFactorizations_zero, Finset.card_empty, Nat.cast_zero]
    positivity
  · exact hc n hn

end
end DivisorProof


/-! ## Shift Counting -/

/-! Counting the actual seven-variable relation by two ternary factorizations. -/
namespace DivisorProof
open Finset Set Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

def shiftedProduct (positive : Bool) (u h : ℕ) : ℕ := if positive then u-h else u+h

theorem signed_relation_right_product (positive : Bool) {n : Fin 7 → ℕ}
    (hrel : signedQuadraticRelation positive n) :
    n 1*n 4*n 5 = shiftedProduct positive (n 0*n 2*n 3) (n 6) := by
  have hcast : ((n 0*n 2*n 3 : ℕ) : ℤ)-((n 1*n 4*n 5 : ℕ) : ℤ) =
      if positive then (n 6 : ℤ) else -(n 6 : ℤ) := by
    push_cast
    exact hrel
  cases positive <;> simp only [shiftedProduct, Bool.false_eq_true, ite_false, ite_true] at hcast ⊢
  all_goals omega

/-- Each `(u,h)` fiber embeds into the two actual ternary factorization sets. -/
theorem signed_tuple_fiber_card_le (s : Finset (Fin 7 → ℕ))
    (positive : Bool) (hpos : ∀ n ∈ s, ∀ j, 0 < n j)
    (hrel : ∀ n ∈ s, signedQuadraticRelation positive n) (u h : ℕ) :
    (s.filter (fun n => (n 0*n 2*n 3, n 6) = (u, h))).card ≤
      (tripleFactorizations u).card*(tripleFactorizations (shiftedProduct positive u h)).card := by
  calc
    _ ≤ ((tripleFactorizations u) ×ˢ (tripleFactorizations (shiftedProduct positive u h))).card := by
      apply card_le_card_of_injOn
        (fun n : Fin 7 → ℕ => ((n 0, n 2, n 3), (n 1, n 4, n 5)))
      · intro n hn
        obtain ⟨hns, hnuh⟩ := mem_filter.mp hn
        have hu : n 0*n 2*n 3 = u := congrArg (fun z : ℕ × ℕ => z.1) hnuh
        have hh : n 6 = h := congrArg (fun z : ℕ × ℕ => z.2) hnuh
        apply mem_product.mpr
        constructor
        · exact mem_tripleFactorizations.mpr ⟨hpos n hns 0, hpos n hns 2, hpos n hns 3, hu⟩
        · apply mem_tripleFactorizations.mpr
          refine ⟨hpos n hns 1, hpos n hns 4, hpos n hns 5, ?_⟩
          simpa only [hu, hh] using signed_relation_right_product positive (hrel n hns)
      · intro n hn n' hn' heq
        have hh : n 6 = h := congrArg (fun z : ℕ × ℕ => z.2) (mem_filter.mp hn).2
        have hh' : n' 6 = h := congrArg (fun z : ℕ × ℕ => z.2) (mem_filter.mp hn').2
        simp only [Prod.mk.injEq] at heq
        obtain ⟨⟨ha, hm₁, hm₂⟩, hb, hn₁, hn₂⟩ := heq
        funext j
        fin_cases j
        · exact ha
        · exact hb
        · exact hm₁
        · exact hm₂
        · exact hn₁
        · exact hn₂
        · exact hh.trans hh'.symm
    _ = _ := card_product _ _

/-- Uniform counting of all tuples satisfying the signed relation.
The constant is obtained from a proved divisor bound, for either sign. -/
theorem signed_tuple_count_subpower {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset (Fin 7 → ℕ)) (positive : Bool) (U H : ℕ),
      (∀ n ∈ s, ∀ j, 0 < n j) →
      (∀ n ∈ s, signedQuadraticRelation positive n) →
      (∀ n ∈ s, n 0*n 2*n 3 ≤ U) → (∀ n ∈ s, n 6 ≤ H) →
      (s.card : ℝ) ≤ (U : ℝ)*H*(C*((U+H : ℕ) : ℝ)^ρ)^2 := by
  obtain ⟨C, hC, hc⟩ := tripleFactorizations_subpower_all hρ
  refine ⟨C, hC, ?_⟩
  intro s positive U H hpos hrel hU hH
  let f : (Fin 7 → ℕ) → ℕ × ℕ := fun n => (n 0*n 2*n 3, n 6)
  let t : Finset (ℕ × ℕ) := (Finset.Icc 1 U) ×ˢ (Finset.Icc 1 H)
  have hmaps : (s : Set (Fin 7 → ℕ)).MapsTo f t := by
    intro n hn
    exact mem_product.mpr ⟨Finset.mem_Icc.mpr
      ⟨Nat.mul_pos (Nat.mul_pos (hpos n hn 0) (hpos n hn 2)) (hpos n hn 3), hU n hn⟩,
      Finset.mem_Icc.mpr ⟨hpos n hn 6, hH n hn⟩⟩
  have hsingle (n : ℕ) (hn : n ≤ U+H) :
      ((tripleFactorizations n).card : ℝ) ≤ C*((U+H : ℕ) : ℝ)^ρ := by
    apply (hc n).trans
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hn) hρ.le
  have hfiber (p : ℕ × ℕ) (hp : p ∈ t) :
      ((s.filter (fun n => f n = p)).card : ℝ) ≤ (C*((U+H : ℕ) : ℝ)^ρ)^2 := by
    have hpU := (Finset.mem_Icc.mp (mem_product.mp hp).1).2
    have hpH := (Finset.mem_Icc.mp (mem_product.mp hp).2).2
    have hright : shiftedProduct positive p.1 p.2 ≤ U+H := by
      cases positive <;> simp only [shiftedProduct, Bool.false_eq_true, ite_false, ite_true] <;> omega
    have hcard : ((s.filter (fun n => f n = p)).card : ℝ) ≤
        ((tripleFactorizations p.1).card : ℝ)*
          (tripleFactorizations (shiftedProduct positive p.1 p.2)).card := by
      exact_mod_cast signed_tuple_fiber_card_le s positive hpos hrel p.1 p.2
    apply hcard.trans
    rw [pow_two]
    exact mul_le_mul (hsingle p.1 (by omega)) (hsingle _ hright) (Nat.cast_nonneg _)
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  rw [card_eq_sum_card_fiberwise hmaps, Nat.cast_sum]
  calc _ ≤ ∑ _p ∈ t, (C*((U+H : ℕ) : ℝ)^ρ)^2 := sum_le_sum hfiber
    _ = (U : ℝ)*H*(C*((U+H : ℕ) : ℝ)^ρ)^2 := by
      simp only [sum_const, nsmul_eq_mul, t, card_product, Nat.card_Icc,
        Nat.add_sub_cancel, Nat.cast_mul]

end
end DivisorProof


/-! ## Shift Error -/

/-! Quantitative summation of the weight-shift error over the actual signed relation. -/
namespace DivisorProof
open Finset Set Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

/-- Real-scale version of the full tuple count; the two factorization costs
are kept uniform over the complete finite sum. -/
theorem signed_tuple_count_real {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset (Fin 7 → ℕ)) (positive : Bool) (U H Q K : ℝ),
      0 ≤ U → 0 ≤ H → 0 ≤ Q → 0 ≤ K → U ≤ Q → H ≤ K*Q →
      (∀ n ∈ s, ∀ j, 0 < n j) →
      (∀ n ∈ s, signedQuadraticRelation positive n) →
      (∀ n ∈ s, (n 0 : ℝ)*n 2*n 3 ≤ 8*U) → (∀ n ∈ s, (n 6 : ℝ) ≤ 2*H) →
      (s.card : ℝ) ≤ 16*U*H*(C*((8+2*K)*Q)^ρ)^2 := by
  obtain ⟨C, hC, hc⟩ := signed_tuple_count_subpower hρ
  refine ⟨C, hC, ?_⟩
  intro s positive U H Q K hU hH hQ hK hUQ hHQ hpos hrel hleft hshift
  have hleft' (n) (hn : n ∈ s) : n 0*n 2*n 3 ≤ ⌊8*U⌋₊ := by
    apply (Nat.le_floor_iff (mul_nonneg (by norm_num) hU)).mpr
    exact_mod_cast hleft n hn
  have hshift' (n) (hn : n ∈ s) : n 6 ≤ ⌊2*H⌋₊ :=
    (Nat.le_floor_iff (mul_nonneg (by norm_num) hH)).mpr (hshift n hn)
  have hcount := hc s positive ⌊8*U⌋₊ ⌊2*H⌋₊ hpos hrel hleft' hshift'
  have hfloorU := Nat.floor_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hU)
  have hfloorH := Nat.floor_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hH)
  have hsum : ((⌊8*U⌋₊+⌊2*H⌋₊ : ℕ) : ℝ) ≤ (8+2*K)*Q := by
    push_cast
    nlinarith
  have hpow : C*((⌊8*U⌋₊+⌊2*H⌋₊ : ℕ) : ℝ)^ρ ≤ C*((8+2*K)*Q)^ρ :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hsum hρ.le) hC
  apply hcount.trans
  calc
    (⌊8*U⌋₊ : ℝ)*⌊2*H⌋₊*(C*((⌊8*U⌋₊+⌊2*H⌋₊ : ℕ) : ℝ)^ρ)^2 ≤
        (8*U)*(2*H)*(C*((8+2*K)*Q)^ρ)^2 := by
      apply mul_le_mul (mul_le_mul hfloorU hfloorH (Nat.cast_nonneg _) (by positivity))
        (pow_le_pow_left₀ (by positivity) hpow 2) (sq_nonneg _) (by positivity)
    _ = _ := by ring

/-- A signed shift has the literal nonnegative shift as its absolute value. -/
theorem abs_signed_shift (positive : Bool) (h : ℕ) :
    |(if positive then (h : ℝ) else -(h : ℝ))| = (h : ℝ) := by
  cases positive <;> simp

/-- The Diophantine relation identifies the original final weight argument. -/
theorem original_weight_argument (positive : Bool) {n : Fin 7 → ℕ}
    (hrel : signedQuadraticRelation positive n) (N : ℝ)
    (hn₁ : n 1 ≠ 0) (hn₄ : n 4 ≠ 0) :
    (n 5 : ℝ)/N =
      ((n 0 : ℝ)*n 2*n 3-(if positive then (n 6 : ℝ) else -(n 6 : ℝ)))/
        ((n 1 : ℝ)*n 4*N) := by
  have hcast : (n 0 : ℝ)*n 2*n 3-(n 1 : ℝ)*n 4*n 5 =
      if positive then (n 6 : ℝ) else -(n 6 : ℝ) := by
    cases positive <;>
      simp only [signedQuadraticRelation, Bool.false_eq_true, ite_false, ite_true] at hrel ⊢
    all_goals exact_mod_cast hrel
  have heq : (n 0 : ℝ)*n 2*n 3-(if positive then (n 6 : ℝ) else -(n 6 : ℝ)) =
      (n 1 : ℝ)*n 4*n 5 := by linarith
  rw [heq]
  have h₁ : (n 1 : ℝ) ≠ 0 := by exact_mod_cast hn₁
  have h₄ : (n 4 : ℝ) ≠ 0 := by exact_mod_cast hn₄
  by_cases hN : N = 0
  · simp [hN]
  · field_simp

/-- Pointwise shift removal on a true arithmetic solution, with the original
weight argument `n₂/N₂` on the left. -/
theorem relation_weight_shift_bound {W : ℝ → ℝ} (hW : SmoothDyadicWeight W)
    {b : ℝ} (hder : ∀ x, ‖iteratedDeriv 1 W x‖ ≤ b)
    (positive : Bool) {n : Fin 7 → ℕ} (hpos : ∀ j, 0 < n j)
    (hrel : signedQuadraticRelation positive n) {N V H : ℝ}
    (hN : 0 < N) (hV : 0 < V) (hH : (n 6 : ℝ) ≤ 2*H)
    (hden : V ≤ (n 1 : ℝ)*n 4*N) :
    ‖W ((n 5 : ℝ)/N)-W ((n 0 : ℝ)*n 2*n 3/((n 1 : ℝ)*n 4*N))‖ ≤ 2*b*H/V := by
  have hb : 0 ≤ b := (norm_nonneg _).trans (hder 0)
  have h₁ : (0 : ℝ) < n 1 := by exact_mod_cast hpos 1
  have h₄ : (0 : ℝ) < n 4 := by exact_mod_cast hpos 4
  have hdenp : 0 < (n 1 : ℝ)*n 4*N := by positivity
  rw [original_weight_argument positive hrel N (hpos 1).ne' (hpos 4).ne']
  apply (weight_shift_bound hW hder _ _ hdenp).trans
  rw [abs_signed_shift]
  calc b*(n 6 : ℝ)/((n 1 : ℝ)*n 4*N) ≤ b*(2*H)/((n 1 : ℝ)*n 4*N) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hH hb) hdenp.le
    _ ≤ b*(2*H)/V := div_le_div_of_nonneg_left
      (mul_nonneg hb ((Nat.cast_nonneg (n 6)).trans hH)) hV hden
    _ = _ := by ring

/-- The summed replacement error is `O(Q^(2ρ) H²)`.  All tuple counting and
mean-value premises are discharged by the preceding proved lemmas. -/
theorem summed_weight_shift_error {ρ K P b : ℝ} (hρ : 0 < ρ)
    (hK : 0 ≤ K) (hP : 0 ≤ P) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Finset (Fin 7 → ℕ)) (positive : Bool)
      (U H Q N V : ℝ) (W : ℝ → ℝ) (w : (Fin 7 → ℕ) → ℂ),
      0 < U → 0 ≤ H → 0 < Q → 0 < N → 0 < V → U ≤ Q → H ≤ K*Q → U ≤ K*V →
      SmoothDyadicWeight W → (∀ x, ‖iteratedDeriv 1 W x‖ ≤ b) →
      (∀ n ∈ s, ∀ j, 0 < n j) → (∀ n ∈ s, signedQuadraticRelation positive n) →
      (∀ n ∈ s, (n 0 : ℝ)*n 2*n 3 ≤ 8*U) → (∀ n ∈ s, (n 6 : ℝ) ≤ 2*H) →
      (∀ n ∈ s, V ≤ (n 1 : ℝ)*n 4*N) → (∀ n ∈ s, ‖w n‖ ≤ P) →
      ‖∑ n ∈ s, w n*((W ((n 5 : ℝ)/N) : ℂ)-
        (W ((n 0 : ℝ)*n 2*n 3/((n 1 : ℝ)*n 4*N)) : ℂ))‖ ≤ C*Q^(2*ρ)*H^2 := by
  obtain ⟨D, hD, hcount⟩ := signed_tuple_count_real hρ
  refine ⟨32*P*b*K*D^2*(8+2*K)^(2*ρ), by positivity, ?_⟩
  intro s positive U H Q N V W w hU hH hQ hN hV hUQ hHQ hUV hW hder hpos hrel hleft hshift hden hw
  have hc := hcount s positive U H Q K hU.le hH hQ.le hK hUQ hHQ hpos hrel hleft hshift
  have herr (n) (hn : n ∈ s) : ‖w n*((W ((n 5 : ℝ)/N) : ℂ)-
      (W ((n 0 : ℝ)*n 2*n 3/((n 1 : ℝ)*n 4*N)) : ℂ))‖ ≤ P*(2*b*H/V) := by
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real]
    exact mul_le_mul (hw n hn) (relation_weight_shift_bound hW hder positive (hpos n hn)
      (hrel n hn) hN hV (hshift n hn) (hden n hn)) (norm_nonneg _) hP
  have hsum : ‖∑ n ∈ s, w n*((W ((n 5 : ℝ)/N) : ℂ)-
      (W ((n 0 : ℝ)*n 2*n 3/((n 1 : ℝ)*n 4*N)) : ℂ))‖ ≤
      (16*U*H*(D*((8+2*K)*Q)^ρ)^2)*(P*(2*b*H/V)) := by
    calc _ ≤ ∑ n ∈ s, ‖w n*((W ((n 5 : ℝ)/N) : ℂ)-
        (W ((n 0 : ℝ)*n 2*n 3/((n 1 : ℝ)*n 4*N)) : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ s, P*(2*b*H/V) := sum_le_sum herr
      _ = (s.card : ℝ)*(P*(2*b*H/V)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  apply hsum.trans
  have hUV' : U/V ≤ K := (div_le_iff₀ hV).mpr hUV
  have heq : (D*((8+2*K)*Q)^ρ)^2 = D^2*(8+2*K)^(2*ρ)*Q^(2*ρ) := by
    calc (D*((8+2*K)*Q)^ρ)^2 = D^2*((8+2*K)*Q)^(2*ρ) := by
          rw [mul_pow, ← Real.rpow_mul_natCast (by positivity : 0 ≤ (8+2*K)*Q)]
          congr 1
          congr 1
          norm_num
          ring
      _ = _ := by rw [Real.mul_rpow (by positivity) hQ.le]; ring
  rw [heq]
  calc _ = (32*P*b*D^2*(8+2*K)^(2*ρ)*Q^(2*ρ)*H^2)*(U/V) := by ring
    _ ≤ (32*P*b*D^2*(8+2*K)^(2*ρ)*Q^(2*ρ)*H^2)*K :=
      mul_le_mul_of_nonneg_left hUV' (by positivity)
    _ = _ := by ring

end
end DivisorProof


/-! ## Actual Shift -/

/-! Application of the proved replacement estimate to the literal finite divisor sum.
This module keeps its finite index range.  The later RangeExtension and LiftPairs
sections prove the extension to arithmetic progressions and the full normal form.
-/
namespace DivisorProof
open MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

def quadraticPreWeight (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) (n : Fin 7 → ℕ) : ℂ :=
  α (n 0)*β (n 1)*(W 0 (n 6/q.H) : ℂ)*
    (W 1 (n 2/q.M₁) : ℂ)*(W 2 (n 3/q.M₂) : ℂ)*(W 3 (n 4/q.N₁) : ℂ)

def activeSignedIndexSet (positive : Bool) (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) : Finset (Fin 7 → ℕ) :=
  (quadraticIndexSet q).filter (fun n => signedQuadraticRelation positive n ∧
    quadraticPreWeight q α β W n ≠ 0)

def shiftRemovedFiniteSum (positive : Bool) (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) : ℂ :=
  ∑ n ∈ activeSignedIndexSet positive q α β W, quadraticPreWeight q α β W n *
    (W 4 ((n 0 : ℝ)*n 2*n 3/((n 1 : ℝ)*n 4*q.N₂)) : ℂ)

theorem quadraticSum_eq_active (positive : Bool) (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) :
    signedQuadraticSum positive q α β W =
      ∑ n ∈ activeSignedIndexSet positive q α β W,
        quadraticPreWeight q α β W n*(W 4 (n 5/q.N₂) : ℂ) := by
  unfold signedQuadraticSum activeSignedIndexSet
  rw [sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hrel : signedQuadraticRelation positive n
  · by_cases hw : quadraticPreWeight q α β W n = 0
    · simp only [hrel, hw, ne_eq, not_true_eq_false, and_false, ite_true, ite_false]
      change quadraticPreWeight q α β W n*(W 4 (n 5/q.N₂) : ℂ) = 0
      rw [hw, zero_mul]
    · simp only [hrel, hw, ne_eq, not_false_eq_true, and_self, ite_true]
      rfl
  · simp only [hrel, false_and, ite_false]

theorem quadraticIndexSet_coordinate_bounds (q : QuadraticScales)
    (h : ∀ j, 1 ≤ q.size j) {n : Fin 7 → ℕ} (hn : n ∈ quadraticIndexSet q) (j : Fin 7) :
    0 < n j ∧ (n j : ℝ) ≤ 2*q.size j := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp ((Fintype.mem_piFinset.mp hn) j)
  have hhi' : (n j : ℝ) ≤ (⌊2*q.size j⌋₊ : ℝ) := by exact_mod_cast hhi
  exact ⟨hlo, hhi'.trans (Nat.floor_le (by linarith [h j]))⟩

theorem quadraticPreWeight_norm_le (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) {b₀ : ℝ} (hb₀ : 0 ≤ b₀)
    (hα : ∀ n, ‖α n‖ ≤ 1) (hβ : ∀ n, ‖β n‖ ≤ 1)
    (hW : ∀ i x, ‖W i x‖ ≤ b₀) (n : Fin 7 → ℕ) :
    ‖quadraticPreWeight q α β W n‖ ≤ b₀^4 := by
  unfold quadraticPreWeight
  simp only [norm_mul, Complex.norm_real]
  calc
    _ ≤ 1*1*b₀*b₀*b₀*b₀ := by
      gcongr
      · exact hα _
      · exact hβ _
      · exact hW _ _
      · exact hW _ _
      · exact hW _ _
      · exact hW _ _
    _ = _ := by ring

/-- The unchanged finite sum satisfies the claimed `Λ²H²` replacement bound.
This local theorem keeps the old range; the following RangeExtension section
proves the stronger estimate on the enlarged range. -/
theorem actual_finite_weight_shift_error {ρ K b₀ b₁ : ℝ}
    (hρ : 0 < ρ) (hK : 1 ≤ K) (hb₀ : 0 ≤ b₀) (hb₁ : 0 ≤ b₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (positive : Bool) (q : QuadraticScales)
      (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
      (∀ j, 1 ≤ q.size j) → q.H ≤ K*q.mass → q.A*q.M ≤ K*q.B*q.N →
      (∀ n : ℕ, (n : ℝ) ∉ Icc q.B (2*q.B) → β n = 0) →
      (∀ n, ‖α n‖ ≤ 1) → (∀ n, ‖β n‖ ≤ 1) →
      (∀ i, SmoothDyadicWeight (W i)) → (∀ i x, ‖W i x‖ ≤ b₀) →
      (∀ x, ‖iteratedDeriv 1 (W 4) x‖ ≤ b₁) →
      ‖signedQuadraticSum positive q α β W-shiftRemovedFiniteSum positive q α β W‖ ≤
        C*q.mass^(2*ρ)*q.H^2 := by
  obtain ⟨C, hC, hc⟩ := summed_weight_shift_error (P := b₀^4) (b := b₁) hρ
    (by linarith : 0 ≤ K) (by positivity) hb₁
  refine ⟨C, hC, ?_⟩
  intro positive q α β W h hH hbalance hsupp hα hβ hW hWnorm hder
  let s := activeSignedIndexSet positive q α β W
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hM₁ : 0 < q.M₁ := lt_of_lt_of_le (by norm_num) (h 2)
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN₁ : 0 < q.N₁ := lt_of_lt_of_le (by norm_num) (h 4)
  have hN₂ : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
  have hH0 : 0 ≤ q.H := zero_le_one.trans (h 6)
  have hQ := (poisson_scale_bounds q h).1
  have hU : 0 < q.A*q.M := by dsimp [QuadraticScales.M]; positivity
  have hV : 0 < q.B*q.N := by dsimp [QuadraticScales.N]; positivity
  have hN : 1 ≤ q.B*q.N := by
    dsimp [QuadraticScales.N]
    exact one_le_mul_of_one_le_of_one_le (h 1) (one_le_mul_of_one_le_of_one_le (h 4) (h 5))
  have hUQ : q.A*q.M ≤ q.mass := by
    rw [mass_eq_balanced_product]
    exact le_mul_of_one_le_right hU.le hN
  have hnset {n} (hn : n ∈ s) : n ∈ quadraticIndexSet q := (mem_filter.mp hn).1
  have hpos : ∀ n ∈ s, ∀ j, 0 < n j := fun n hn j =>
    (quadraticIndexSet_coordinate_bounds q h (hnset hn) j).1
  have hrel : ∀ n ∈ s, signedQuadraticRelation positive n := fun _ hn =>
    (mem_filter.mp hn).2.1
  have hleft (n) (hn : n ∈ s) : (n 0 : ℝ)*n 2*n 3 ≤ 8*(q.A*q.M) := by
    have h₀ : (n 0 : ℝ) ≤ 2*q.A := (quadraticIndexSet_coordinate_bounds q h (hnset hn) 0).2
    have h₂ : (n 2 : ℝ) ≤ 2*q.M₁ := (quadraticIndexSet_coordinate_bounds q h (hnset hn) 2).2
    have h₃ : (n 3 : ℝ) ≤ 2*q.M₂ := (quadraticIndexSet_coordinate_bounds q h (hnset hn) 3).2
    calc _ ≤ (2*q.A)*(2*q.M₁)*(2*q.M₂) := by gcongr
      _ = _ := by dsimp [QuadraticScales.M]; ring
  have hshift (n) (hn : n ∈ s) : (n 6 : ℝ) ≤ 2*q.H :=
    (quadraticIndexSet_coordinate_bounds q h (hnset hn) 6).2
  have hden (n) (hn : n ∈ s) : q.B*q.N ≤ (n 1 : ℝ)*n 4*q.N₂ := by
    have hpre := (mem_filter.mp hn).2.2
    have hβne : β (n 1) ≠ 0 := by
      intro hz
      exact hpre (by simp [quadraticPreWeight, hz])
    have hβsupport : (n 1 : ℝ) ∈ Icc q.B (2*q.B) := by
      by_contra hn
      exact hβne (hsupp _ hn)
    have h₃ne : W 3 ((n 4 : ℝ)/q.N₁) ≠ 0 := by
      intro hz
      exact hpre (by simp [quadraticPreWeight, hz])
    have h₃support := (hW 3).2 (subset_tsupport (W 3) h₃ne)
    have h₄lower : q.N₁ ≤ (n 4 : ℝ) := by
      simpa only [one_mul] using (le_div_iff₀ hN₁).mp h₃support.1
    calc q.B*q.N = (q.B*q.N₁)*q.N₂ := by dsimp [QuadraticScales.N]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul hβsupport.1 h₄lower hN₁.le (Nat.cast_nonneg _)) hN₂.le
  have hbound := hc s positive (q.A*q.M) q.H q.mass q.N₂ (q.B*q.N) (W 4)
    (quadraticPreWeight q α β W) hU hH0 (by linarith) hN₂ hV hUQ hH
    (by simpa only [mul_assoc] using hbalance) (hW 4) hder hpos hrel hleft hshift hden
    (fun n _ => quadraticPreWeight_norm_le q α β W hb₀ hα hβ hWnorm n)
  rw [quadraticSum_eq_active, shiftRemovedFiniteSum, ← sum_sub_distrib]
  simpa only [s, mul_sub] using hbound

end
end DivisorProof


/-! ## Normalized Data -/

/-! The normalized coefficient and derivative bounds are proved from the original
admissibility hypotheses, without a separate normalization premise. -/
namespace DivisorProof
open MeasureTheory Set
open scoped BigOperators ContDiff
noncomputable section

theorem SmoothDyadicWeight.const_mul {W : ℝ → ℝ} (hW : SmoothDyadicWeight W) (c : ℝ) :
    SmoothDyadicWeight (fun x => c*W x) := by
  refine ⟨contDiff_const.mul hW.1, ?_⟩
  apply closure_minimal _ isClosed_Icc
  intro x hx
  apply hW.2
  apply subset_tsupport W
  intro hz
  exact hx (by dsimp only; rw [hz, mul_zero])

theorem normalized_coefficient_norm_le {α : ℕ → ℂ} {C : ℝ} (hC : 0 < C)
    (hα : ∀ n, ‖α n‖ ≤ C) (n : ℕ) : ‖α n/(C : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hC.le]
  exact (div_le_one hC).mpr (hα n)

theorem normalized_weight_derivative_le {W : ℝ → ℝ} {Q ρ b : ℝ}
    (hQ : 0 < Q) (j : ℕ) (hder : ∀ x, ‖iteratedDeriv j W x‖ ≤ b*Q^ρ) (x : ℝ) :
    ‖iteratedDeriv j (fun y => Q^(-ρ)*W y) x‖ ≤ b := by
  rw [iteratedDeriv_normalized_weight, norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg hQ.le _)]
  calc Q^(-ρ)*‖iteratedDeriv j W x‖ ≤ Q^(-ρ)*(b*Q^ρ) :=
      mul_le_mul_of_nonneg_left (hder x) (Real.rpow_nonneg hQ.le _)
    _ = b := by
      rw [Real.rpow_neg hQ.le]
      have hpow : Q^ρ ≠ 0 := (Real.rpow_pos_of_pos hQ _).ne'
      field_simp

structure NormalizedWeightData (bounds : ℕ → ℝ) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) : Prop where
  alpha_support : ∀ n : ℕ, (n : ℝ) ∉ Icc q.A (2*q.A) → α n = 0
  beta_support : ∀ n : ℕ, (n : ℝ) ∉ Icc q.B (2*q.B) → β n = 0
  alpha_bound : ∀ n, ‖α n‖ ≤ 1
  beta_bound : ∀ n, ‖β n‖ ≤ 1
  smooth : ∀ i, SmoothDyadicWeight (W i)
  derivatives : ∀ j i x, ‖iteratedDeriv j (W i) x‖ ≤ bounds j

theorem admissible_normalized_weight_data {ρ δ K : ℝ} (hK : 1 ≤ K)
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ}
    (hadm : QuadraticAdmissible ρ δ K bounds q α β W) :
    NormalizedWeightData bounds q
      (fun n => α n/((K*q.A^ρ : ℝ) : ℂ))
      (fun n => β n/((K*q.B^ρ : ℝ) : ℂ))
      (fun i x => q.mass^(-ρ)*W i x) := by
  obtain ⟨h, _, _, _, _, _, _, _, hsα, hsβ, hbα, hbβ, hW, hd⟩ := hadm
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num)
    ((product_AB_le_mass q h).1.trans (product_AB_le_mass q h).2)
  have hKp : 0 < K := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rw [hsα n hn, zero_div]
  · intro n hn
    rw [hsβ n hn, zero_div]
  · exact normalized_coefficient_norm_le (mul_pos hKp (Real.rpow_pos_of_pos hA _)) hbα
  · exact normalized_coefficient_norm_le (mul_pos hKp (Real.rpow_pos_of_pos hB _)) hbβ
  · intro i
    exact SmoothDyadicWeight.const_mul (hW i) _
  · intro j i x
    exact normalized_weight_derivative_le hQ j (fun y => hd j i y) x

theorem NormalizedWeightData.bounds_nonneg {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ} (h : NormalizedWeightData bounds q α β W)
    (j : ℕ) : 0 ≤ bounds j := (norm_nonneg _).trans (h.derivatives j 0 0)

theorem NormalizedWeightData.weight_norm {bounds : ℕ → ℝ} {q : QuadraticScales}
    {α β : ℕ → ℂ} {W : Fin 5 → ℝ → ℝ} (h : NormalizedWeightData bounds q α β W)
    (i : Fin 5) (x : ℝ) : ‖W i x‖ ≤ bounds 0 := by
  simpa only [iteratedDeriv_zero] using h.derivatives 0 i x

/-- The finite-range replacement error now follows from exactly the original
admissibility data, after the proved normalization. -/
theorem admissible_normalized_shift_error {ρ δ K : ℝ}
    (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hK : 1 ≤ K) (bounds : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (positive : Bool) (q : QuadraticScales)
      (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
      QuadraticAdmissible ρ δ K bounds q α β W →
      ‖signedQuadraticSum positive q
          (fun n => α n/((K*q.A^ρ : ℝ) : ℂ))
          (fun n => β n/((K*q.B^ρ : ℝ) : ℂ))
          (fun i x => q.mass^(-ρ)*W i x) -
        shiftRemovedFiniteSum positive q
          (fun n => α n/((K*q.A^ρ : ℝ) : ℂ))
          (fun n => β n/((K*q.B^ρ : ℝ) : ℂ))
          (fun i x => q.mass^(-ρ)*W i x)‖ ≤ C*q.mass^(2*ρ)*q.H^2 := by
  obtain ⟨C, hC, hc⟩ := actual_finite_weight_shift_error hρ hK
    (b₀ := max (bounds 0) 0) (b₁ := max (bounds 1) 0)
    (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro positive q α β W hadm
  have hn := admissible_normalized_weight_data hK hadm
  obtain ⟨h, _, _, hH, _, hbal, _, _, _, _, _, _, _, _⟩ := hadm
  exact hc positive q _ _ _ h
    (shiftScale_le_mass q h (by linarith : 0 ≤ K) hρhalf hH) hbal hn.beta_support
    hn.alpha_bound hn.beta_bound hn.smooth
    (fun i x => (hn.weight_norm i x).trans (le_max_left _ _))
    (fun x => (hn.derivatives 1 4 x).trans (le_max_left _ _))

end
end DivisorProof


/-! ## Actual Poisson -/

/-! The arithmetic and analytic Poisson lemmas combined for the literal inner
equation, with the gcd derived from its original two coefficients. -/
namespace DivisorProof
open MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 800000

def reducedEquationTerm (W₂ W₄ : ℝ → ℝ) (A B : ℕ) (M N : ℝ) (k m : ℤ) : ℂ :=
  if ∃ n : ℤ, (A : ℤ)*m-(B : ℤ)*n = (Nat.gcd A B : ℤ)*k then
    (W₂ ((m : ℝ)/M) : ℂ)*(W₄ ((A : ℝ)*m/((B : ℝ)*N)) : ℂ) else 0

def reducedEquationSum (W₂ W₄ : ℝ → ℝ) (A B : ℕ) (M N : ℝ) (k : ℤ) : ℂ :=
  ∑' m : ℤ, reducedEquationTerm W₂ W₄ A B M N k m

/-- The spatial series is a genuine finite sum as a consequence of support. -/
theorem reducedEquationTerm_hasFiniteSupport {W₂ W₄ : ℝ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (A B : ℕ) {M N : ℝ} (hM : 0 < M) (k : ℤ) :
    Function.HasFiniteSupport (reducedEquationTerm W₂ W₄ A B M N k) := by
  apply (frequencySet (2*M)).finite_toSet.subset
  intro m hm
  have hWne : W₂ ((m : ℝ)/M) ≠ 0 := by
    intro hz
    exact hm (by simp [reducedEquationTerm, hz])
  have hs := h₂.2 (subset_tsupport W₂ hWne)
  have hlo : M ≤ (m : ℝ) := by simpa only [one_mul] using (le_div_iff₀ hM).mp hs.1
  have hhi : (m : ℝ) ≤ 2*M := (div_le_iff₀ hM).mp hs.2
  apply (mem_frequencySet (2*M) m).mpr
  rw [abs_of_nonneg (hM.le.trans hlo)]
  exact hhi

theorem gcd_reduced_real_slope (A B : ℕ) (M : ℝ) :
    (((B/Nat.gcd A B : ℕ) : ℝ)/M) = (B : ℝ)/((Nat.gcd A B : ℝ)*M) := by
  rw [Nat.cast_div_charZero (Nat.gcd_dvd_right A B), div_div]

theorem gcd_reduced_other_slope (A B : ℕ) (N : ℝ) :
    (((A/Nat.gcd A B : ℕ) : ℝ)/N) = (A : ℝ)/((Nat.gcd A B : ℝ)*N) := by
  rw [Nat.cast_div_charZero (Nat.gcd_dvd_left A B), div_div]

theorem gcd_reduced_real_ratio (A B : ℕ) (hB : 0 < B) {N : ℝ} (hN : 0 < N) (m : ℝ) :
    (((A/Nat.gcd A B : ℕ) : ℝ)*m/(((B/Nat.gcd A B : ℕ) : ℝ)*N)) =
      (A : ℝ)*m/((B : ℝ)*N) := by
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hd0 : (Nat.gcd A B : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.gcd_pos_of_pos_right A hB).ne'
  rw [Nat.cast_div_charZero (Nat.gcd_dvd_left A B),
    Nat.cast_div_charZero (Nat.gcd_dvd_right A B)]
  field_simp

/-- Exact passage from the original integer equation to the profile lattice. -/
theorem reducedEquationSum_eq_profile_lattice {W₂ W₄ : ℝ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (A B : ℕ) (hB : 0 < B) {M N : ℝ} (hM : 0 < M) (hN : 0 < N) (k : ℤ) :
    reducedEquationSum W₂ W₄ A B M N k =
      ∑' j : ℤ, poissonProfile W₂ W₄ ((B : ℝ)/((Nat.gcd A B : ℝ)*M))
        ((A : ℝ)/((Nat.gcd A B : ℝ)*N))
          ((k : ℝ)*(inverseRepresentative (A/Nat.gcd A B) (B/Nat.gcd A B) : ℝ)/
            ((B/Nat.gcd A B : ℕ) : ℝ)+j) := by
  have hp := poisson_original_equation_identity h₂ h₄ A B hB hM hN k
  simp_rw [gcd_reduced_real_ratio A B hB hN, gcd_reduced_real_slope,
    gcd_reduced_other_slope] at hp
  change reducedEquationSum W₂ W₄ A B M N k = _ at hp
  apply hp.trans
  symm
  have hBp : (0 : ℝ) < B := by exact_mod_cast hB
  have hdp : (0 : ℝ) < Nat.gcd A B := by exact_mod_cast Nat.gcd_pos_of_pos_right A hB
  exact poisson_profile_identity h₂ h₄ (div_pos hBp (mul_pos hdp hM)).ne' _

/-- The fully combined one-tuple form of (19)–(23), with the original arithmetic
equation and a uniform power-saving remainder.  The signed shift is `d*k`,
where `k` may have either sign. -/
theorem finite_poisson_actual_inner {W₂ W₄ : ℝ → ℝ} {bounds : ℕ → ℝ}
    (h₂ : SmoothDyadicWeight W₂) (h₄ : SmoothDyadicWeight W₄)
    (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j)
    (A B : ℕ) (hB : 0 < B) {K ρ : ℝ} (hK : 1 ≤ K) (hρ : 0 < ρ)
    (hAupper : (A : ℝ) ≤ 4*q.A*q.M₁)
    (hBlower : q.B*q.N₁ ≤ (B : ℝ)) (hBupper : (B : ℝ) ≤ 4*q.B*q.N₁)
    (hbalance₁ : q.A*q.M ≤ K*q.B*q.N) (hbalance₂ : q.B*q.N ≤ K*q.A*q.M)
    (hder₂ : ∀ j x, ‖iteratedDeriv j W₂ x‖ ≤ bounds j)
    (hder₄ : ∀ j x, ‖iteratedDeriv j W₄ x‖ ≤ bounds j) (k : ℤ) :
    ‖(reducedEquationSum W₂ W₄ A B q.M₂ q.N₂ k -
        ∫ x : ℝ in Ioi 0, poissonProfile W₂ W₄
          ((B : ℝ)/((Nat.gcd A B : ℝ)*q.M₂))
          ((A : ℝ)/((Nat.gcd A B : ℝ)*q.N₂)) x) -
      ∫ x : ℝ in Ioi 0, poissonProfile W₂ W₄
        ((B : ℝ)/((Nat.gcd A B : ℝ)*q.M₂))
        ((A : ℝ)/((Nat.gcd A B : ℝ)*q.N₂)) x *
        finitePoissonKernel (poissonLength q ρ (Nat.gcd A B : ℝ))
          ((k : ℝ)*(inverseRepresentative (A/Nat.gcd A B) (B/Nat.gcd A B) : ℝ)/
            ((B/Nat.gcd A B : ℕ) : ℝ)) x‖ ≤
      (2*profileFourierBound bounds (4*K) (truncationOrder ρ+2)*
        K^(truncationOrder ρ)*inverseSquareMass)/q.mass^9 := by
  have hM₂ : 0 < q.M₂ := lt_of_lt_of_le (by norm_num) (h 3)
  have hN₂ : 0 < q.N₂ := lt_of_lt_of_le (by norm_num) (h 5)
  rw [reducedEquationSum_eq_profile_lattice h₂ h₄ A B hB hM₂ hN₂]
  have hd : (1 : ℝ) ≤ Nat.gcd A B := by exact_mod_cast Nat.gcd_pos_of_pos_right A hB
  exact finite_poisson_dyadic_remainder h₂ h₄ q h hK hρ hd
    (Nat.cast_nonneg A) hAupper hBlower hBupper hbalance₁ hbalance₂ hder₂ hder₄ _

end
end DivisorProof
