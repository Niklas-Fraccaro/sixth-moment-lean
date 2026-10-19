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
import Sechstmoment.Arithmetic.Divisors.Subpower
import Sechstmoment.Arithmetic.Kloosterman.Estermann
import Sechstmoment.Arithmetic.QuadraticDivisor.Estimates.SourceAdapter
import Std


/-!
# Divisor estimates used by the Watt reduction

New arithmetic and analytic proofs from the supplied divisor-sum project
(Leanfreundlicher_Divisorsummenbeweis.pdf, 15 October 2026).
The borrowed source definitions, divisor subpower lemma and scalar transfer
lemmas are imported from the existing Sechstmoment modules, not copied.
`DivisorParameters` provides the shared exponent budget. Namespace exports
retain the original proof's notation without introducing duplicate constants.

`DivisorProof.weightedWattBound_of_watt41` derives the intermediate
`WeightedWattBound` from the exact external `DivisorProof.Watt41` proposition.
`Sechstmoment.WattDivisorInput` connects its separated-exponent conclusion
directly to the existing source consumers. SALT's proved Estermann estimate
is connected in `EstermannBridge`; provenance is in `Salt/UPSTREAM.json`.
-/

namespace DivisorProof
export Sechstmoment (SmoothDyadicWeight)
export Sechstmoment.Source (QuadraticScales quadraticIndexSet signedQuadraticRelation
  quadraticSummand signedQuadraticSum quadraticMainIndexSet quadraticZeroModeSummand
  quadraticZeroMode signedQuadraticDiscrepancy orientedQuadraticMajorant QuadraticAdmissible)
namespace QuadraticScales
export Sechstmoment.Source.QuadraticScales (M N mass size)
end QuadraticScales
end DivisorProof

/-! ## Normalization -/

/-! Exact multilinearity in equation (16); the zero mode is retained literally. -/
namespace DivisorProof
open MeasureTheory Set
open scoped BigOperators
noncomputable section

/-- Scaling the two coefficient sequences and all five weights. -/
theorem quadraticSummand_scale (q : QuadraticScales) (α β : ℕ → ℂ)
    (W : Fin 5 → ℝ → ℝ) (cα cβ : ℂ) (cW : ℝ) (n : Fin 7 → ℕ) :
    quadraticSummand q (fun n => cα * α n) (fun n => cβ * β n)
      (fun i x => cW * W i x) n =
    (cα * cβ * (cW : ℂ)^5) * quadraticSummand q α β W n := by
  simp only [quadraticSummand, Complex.ofReal_mul]
  ring

theorem signedQuadraticSum_scale (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (cα cβ : ℂ) (cW : ℝ) :
    signedQuadraticSum positive q (fun n => cα * α n) (fun n => cβ * β n)
      (fun i x => cW * W i x) =
    (cα * cβ * (cW : ℂ)^5) * signedQuadraticSum positive q α β W := by
  classical
  unfold signedQuadraticSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs
  · exact quadraticSummand_scale q α β W cα cβ cW n
  · simp

theorem quadraticZeroModeSummand_scale (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (cα cβ : ℂ) (cW : ℝ)
    (n : Fin 5 → ℕ) :
    quadraticZeroModeSummand q (fun n => cα * α n) (fun n => cβ * β n)
      (fun i x => cW * W i x) n =
    (cα * cβ * (cW : ℂ)^5) * quadraticZeroModeSummand q α β W n := by
  let d : ℝ := Nat.gcd (n 0*n 2) (n 1*n 3)
  have hi : (∫ x : ℝ in Ioi 0,
      ((cW * W 2 (n 1*n 3*x/(d*q.M₂))) : ℂ) *
      ((cW * W 4 (n 0*n 2*x/(d*q.N₂))) : ℂ)) =
      (cW : ℂ)^2 * (∫ x : ℝ in Ioi 0,
      (W 2 (n 1*n 3*x/(d*q.M₂)) : ℂ) *
      (W 4 (n 0*n 2*x/(d*q.N₂)) : ℂ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  dsimp only [quadraticZeroModeSummand]
  simp only [Complex.ofReal_mul]
  rw [hi]
  dsimp [d]
  ring

theorem quadraticZeroMode_scale (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (cα cβ : ℂ) (cW : ℝ) :
    quadraticZeroMode q (fun n => cα * α n) (fun n => cβ * β n)
      (fun i x => cW * W i x) =
    (cα * cβ * (cW : ℂ)^5) * quadraticZeroMode q α β W := by
  unfold quadraticZeroMode
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun n _ => quadraticZeroModeSummand_scale q α β W cα cβ cW n)

/-- Exact, unconditional algebraic identity for the actual discrepancy. -/
theorem signedQuadraticDiscrepancy_scale (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (cα cβ : ℂ) (cW : ℝ) :
    signedQuadraticDiscrepancy positive q (fun n => cα * α n) (fun n => cβ * β n)
      (fun i x => cW * W i x) =
    (cα * cβ * (cW : ℂ)^5) * signedQuadraticDiscrepancy positive q α β W := by
  unfold signedQuadraticDiscrepancy
  rw [signedQuadraticSum_scale, quadraticZeroMode_scale, mul_sub]

/-- Recovery of the original discrepancy from divided coefficients and weights.
This is the exact multilinear equality underlying (16), for both signs. -/
theorem discrepancy_normalize (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) {cα cβ : ℂ} {cW : ℝ}
    (hα : cα ≠ 0) (hβ : cβ ≠ 0) (hW : cW ≠ 0) :
    signedQuadraticDiscrepancy positive q α β W =
    (cα*cβ*(cW : ℂ)^5) * signedQuadraticDiscrepancy positive q
      (fun n => α n/cα) (fun n => β n/cβ) (fun i x => W i x/cW) := by
  rw [← signedQuadraticDiscrepancy_scale]
  have hα' : (fun n => cα*(α n/cα)) = α := by
    funext n
    field_simp
  have hβ' : (fun n => cβ*(β n/cβ)) = β := by
    funext n
    field_simp
  have hW' : (fun i x => cW*(W i x/cW)) = W := by
    funext i x
    field_simp
  rw [hα', hβ', hW']

/-- Scalar multiplication commutes with every iterated derivative, so the
normalization preserves the derivative order in (8). -/
theorem iteratedDeriv_normalized_weight (W : ℝ → ℝ) (c : ℝ) (j : ℕ) :
    iteratedDeriv j (fun x => c*W x) = fun x => c*iteratedDeriv j W x := by
  funext x
  exact iteratedDeriv_const_mul_field c W

/-- With scales at least one, `AB ≤ Q`. -/
theorem product_AB_le_mass (q : QuadraticScales) (h : ∀ j, 1 ≤ q.size j) :
    1 ≤ q.A*q.B ∧ q.A*q.B ≤ q.mass := by
  have hA : 1 ≤ q.A := h 0
  have hB : 1 ≤ q.B := h 1
  have hM₁ : 1 ≤ q.M₁ := h 2
  have hM₂ : 1 ≤ q.M₂ := h 3
  have hN₁ : 1 ≤ q.N₁ := h 4
  have hN₂ : 1 ≤ q.N₂ := h 5
  have hM : 1 ≤ q.M := one_le_mul_of_one_le_of_one_le hM₁ hM₂
  have hN : 1 ≤ q.N := one_le_mul_of_one_le_of_one_le hN₁ hN₂
  have hAB : 1 ≤ q.A*q.B := one_le_mul_of_one_le_of_one_le hA hB
  refine ⟨hAB, ?_⟩
  dsimp [QuadraticScales.mass]
  calc q.A*q.B ≤ q.A*q.B*q.M := le_mul_of_one_le_right (by linarith) hM
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hN

/-- The exact real scalar multiplying the normalized discrepancy in (16). -/
theorem normalization_scalar_identity {A B Q K ρ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ : 0 ≤ Q) :
    (K*A^ρ)*(K*B^ρ)*(Q^ρ)^5 = K^2*(A*B)^ρ*Q^(5*ρ) := by
  rw [Real.mul_rpow hA hB, ← Real.rpow_mul_natCast hQ]
  norm_num
  rw [show ρ*5 = 5*ρ by ring]
  ring

/-- Equation (16), literally for the PDF's coefficients and weights. -/
theorem pdf_normalization_identity (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) {K ρ : ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hK : 1 ≤ K) :
    signedQuadraticDiscrepancy positive q α β W =
      ((K^2*(q.A*q.B)^ρ*q.mass^(5*ρ) : ℝ) : ℂ) *
      signedQuadraticDiscrepancy positive q
        (fun n => α n / ((K*q.A^ρ : ℝ) : ℂ))
        (fun n => β n / ((K*q.B^ρ : ℝ) : ℂ))
        (fun i x => q.mass^(-ρ)*W i x) := by
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (h 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (h 1)
  obtain ⟨hAB, hABQ⟩ := product_AB_le_mass q h
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (hAB.trans hABQ)
  have hKp : 0 < K := by linarith
  have hα : ((K*q.A^ρ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos hKp (Real.rpow_pos_of_pos hA ρ)).ne'
  have hβ : ((K*q.B^ρ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos hKp (Real.rpow_pos_of_pos hB ρ)).ne'
  have he := discrepancy_normalize positive q α β W hα hβ
    (Real.rpow_pos_of_pos hQ ρ).ne'
  have hw : (fun i x => W i x/q.mass^ρ) = (fun i x => q.mass^(-ρ)*W i x) := by
    funext i x
    rw [Real.rpow_neg hQ.le]
    ring
  have hf : ((K*q.A^ρ : ℝ) : ℂ)*((K*q.B^ρ : ℝ) : ℂ)*((q.mass^ρ : ℝ) : ℂ)^5 =
      ((K^2*(q.A*q.B)^ρ*q.mass^(5*ρ) : ℝ) : ℂ) := by
    exact_mod_cast normalization_scalar_identity (K := K) (ρ := ρ) hA.le hB.le hQ.le
  rw [hw, hf] at he
  exact he

/-- The renormalization in (16) costs at most `K² Λ⁶`. -/
theorem normalization_factor_le (q : QuadraticScales) {K ρ : ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hρ : 0 ≤ ρ) :
    K^2 * (q.A*q.B)^ρ * q.mass^(5*ρ) ≤ K^2 * (q.mass^ρ)^6 := by
  obtain ⟨hAB, hABQ⟩ := product_AB_le_mass q h
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (hAB.trans hABQ)
  calc _ ≤ K^2 * q.mass^ρ * q.mass^(5*ρ) := by
          gcongr
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hQ, ← Real.rpow_mul_natCast hQ.le]
      congr 2
      norm_num
      ring

end
end DivisorProof


/-! ## Arithmetic -/

/-! Genuine elementary arithmetic lemmas from §3. No Weil/Watt input is assumed. -/
namespace DivisorProof
open Finset
open scoped BigOperators
noncomputable section

/-- Lemma 3.1 for the ordinary divisor count, with a uniform nonnegative constant. -/
theorem divisor_count_subpower {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≠ 0 →
      (n.divisors.card : ℝ) ≤ C * (n : ℝ)^ρ := by
  obtain ⟨C, hC, hc⟩ := Sechstmoment.divisor_prime_cost_subpower hρ (C := 1) le_rfl
  exact ⟨C, hC, fun n hn => by simpa using hc n hn⟩

/-- Two divisor decompositions cost only one prescribed subpower. -/
theorem divisor_count_sq_subpower {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≠ 0 →
      (n.divisors.card : ℝ)^2 ≤ C * (n : ℝ)^ρ := by
  obtain ⟨C, hC, hc⟩ := divisor_count_subpower (ρ := ρ/2) (by positivity)
  refine ⟨C^2, sq_nonneg _, fun n hn => ?_⟩
  calc _ ≤ (C * (n : ℝ)^(ρ/2))^2 := by gcongr; exact hc n hn
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
      congr 2
      norm_num

/-- Counting positive multiples without an additive error term. -/
theorem card_positive_multiples_le (L d : ℕ) (hd : 0 < d) :
    #{l ∈ Icc 1 L | d ∣ l} ≤ L/d := by
  calc
    _ ≤ #(Icc 1 (L/d)) := by
      apply card_le_card_of_injOn (fun l => l/d)
      · intro l hl
        obtain ⟨hl, hdl⟩ := mem_filter.mp hl
        obtain ⟨hl1, hlL⟩ := mem_Icc.mp hl
        apply mem_Icc.mpr
        exact ⟨Nat.div_pos (Nat.le_of_dvd hl1 hdl) hd,
          Nat.div_le_div_right hlL⟩
      · intro l hl l' hl' heq
        have hdl := (mem_filter.mp hl).2
        have hdl' := (mem_filter.mp hl').2
        calc l = d * (l/d) := (Nat.mul_div_cancel' hdl).symm
          _ = d * (l'/d) := congrArg (d * ·) heq
          _ = l' := Nat.mul_div_cancel' hdl'
    _ = L/d := by simp

/-- An integer version of the single-variable gcd average, stronger than needed. -/
theorem sum_gcd_le (L c : ℕ) (hc : c ≠ 0) :
    ∑ l ∈ Icc 1 L, Nat.gcd l c ≤ L*c.divisors.card := by
  calc
    _ ≤ ∑ l ∈ Icc 1 L, ∑ d ∈ c.divisors, if d ∣ l then d else 0 := by
      apply sum_le_sum
      intro l hl
      have hg : Nat.gcd l c ∈ c.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right l c, hc⟩
      have hi := single_le_sum (s := c.divisors)
        (f := fun d => if d ∣ l then d else 0) (fun _ _ => Nat.zero_le _) hg
      simpa [Nat.gcd_dvd_left l c] using hi
    _ = ∑ d ∈ c.divisors, d * #{l ∈ Icc 1 L | d ∣ l} := by
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm]
      simp only [Nat.cast_id]
    _ ≤ ∑ d ∈ c.divisors, L := by
      apply sum_le_sum
      intro d hd
      have hdp : 0 < d := Nat.pos_of_mem_divisors hd
      calc _ ≤ d * (L/d) := Nat.mul_le_mul_left _ (card_positive_multiples_le L d hdp)
        _ ≤ L := Nat.mul_div_le L d
    _ = L*c.divisors.card := by simp [mul_comm]

/-- Double gcd average; the square root in (12) can be bounded by the gcd itself. -/
theorem sum_sum_gcd_le (L U c : ℕ) (hc : c ≠ 0) :
    ∑ l ∈ Icc 1 L, ∑ k ∈ Icc 1 U, Nat.gcd (l*k) c ≤
      L*U*c.divisors.card^2 := by
  have hpoint (l k : ℕ) : Nat.gcd (l*k) c ≤ Nat.gcd l c * Nat.gcd k c := by
    exact Nat.le_of_dvd
      (Nat.mul_pos (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hc))
        (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hc)))
      (Nat.gcd_mul_left_dvd_mul_gcd c l k)
  calc
    _ ≤ ∑ l ∈ Icc 1 L, ∑ k ∈ Icc 1 U, Nat.gcd l c * Nat.gcd k c := by
      apply sum_le_sum
      intro l hl
      exact sum_le_sum (fun k hk => hpoint l k)
    _ = (∑ l ∈ Icc 1 L, Nat.gcd l c) * (∑ k ∈ Icc 1 U, Nat.gcd k c) := by
      rw [sum_mul_sum]
    _ ≤ (L*c.divisors.card)*(U*c.divisors.card) :=
      Nat.mul_le_mul (sum_gcd_le L c hc) (sum_gcd_le U c hc)
    _ = _ := by ring

/-- Lemma 3.2 for integer upper bounds. -/
theorem sum_sum_sqrt_gcd_le (L U c : ℕ) (hc : c ≠ 0) :
    ∑ l ∈ Icc 1 L, ∑ k ∈ Icc 1 U, Real.sqrt (Nat.gcd (l*k) c) ≤
      (L : ℝ)*U*(c.divisors.card : ℝ)^2 := by
  calc
    _ ≤ ∑ l ∈ Icc 1 L, ∑ k ∈ Icc 1 U, (Nat.gcd (l*k) c : ℝ) := by
      apply sum_le_sum
      intro l hl
      apply sum_le_sum
      intro k hk
      apply Real.sqrt_le_self_iff.mpr
      right
      exact_mod_cast Nat.gcd_pos_of_pos_right (l*k) (Nat.pos_of_ne_zero hc)
    _ ≤ _ := by exact_mod_cast sum_sum_gcd_le L U c hc

/-- Harmonic sum bound (14), valid also when the index set is empty. -/
theorem harmonic_sum_le_subpower {ρ Q : ℝ} (hρ : 0 < ρ) (hQ : 1 ≤ Q)
    (D : ℝ) (hD : D ≤ Q) :
    ∑ d ∈ Icc 1 ⌊D⌋₊, (1 : ℝ)/d ≤ (1 + 1/ρ)*Q^ρ := by
  by_cases hD1 : D < 1
  · have hf : ⌊D⌋₊ = 0 := Nat.floor_eq_zero.mpr hD1
    simp [hf]
    positivity
  have hD1' : 1 ≤ D := le_of_not_gt hD1
  have heq : (∑ d ∈ Icc 1 ⌊D⌋₊, (1 : ℝ)/d) = (harmonic ⌊D⌋₊ : ℝ) := by
    simp [harmonic_eq_sum_Icc, one_div]
  rw [heq]
  have hh := harmonic_floor_le_one_add_log D hD1'
  have hlog := Real.log_le_log (by linarith : 0 < D) hD
  have hpower := Real.log_le_rpow_div (by linarith : 0 ≤ Q) hρ
  have hone : 1 ≤ Q^ρ := Real.one_le_rpow hQ hρ.le
  calc _ ≤ 1 + Real.log D := hh
    _ ≤ 1 + Q^ρ/ρ := by linarith
    _ ≤ Q^ρ + Q^ρ/ρ := add_le_add hone le_rfl
    _ = (1+1/ρ)*Q^ρ := by ring

end
end DivisorProof


/-! ## Divisor Simplification -/

/-! The divisor removal in equation (30), including both max branches. -/
namespace DivisorProof
noncomputable section

theorem one_add_product_fourth_root_le {t z : ℝ} (ht : 0 ≤ t) (hz : 0 ≤ z) :
    (1+t*z)^(1/4 : ℝ) ≤ max 1 (t^(1/4 : ℝ)) * (1+z)^(1/4 : ℝ) := by
  have hc : 1+t*z ≤ max 1 t * (1+z) := by
    have h1 : 1 ≤ max 1 t := le_max_left _ _
    have ht' : t ≤ max 1 t := le_max_right _ _
    nlinarith
  calc _ ≤ (max 1 t * (1+z))^(1/4 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hc (by norm_num)
    _ = (max 1 t)^(1/4 : ℝ) * (1+z)^(1/4 : ℝ) :=
          Real.mul_rpow (by positivity) (by positivity)
    _ = _ := by
          by_cases h : t ≤ 1
          · rw [max_eq_left h, Real.one_rpow,
              max_eq_left (Real.rpow_le_one ht h (by norm_num))]
          · have h1 : 1 ≤ t := (lt_of_not_ge h).le
            rw [max_eq_right h1, max_eq_right (Real.one_le_rpow h1 (by norm_num))]

/-- Equation (30), with `d₁ d₂ = d` and the divisor inequalities explicit.
The numerical hypotheses follow from the positive-integer divisor decomposition. -/
theorem divisor_simplification {d d₁ d₂ d₃ M BY : ℝ}
    (hd₁ : 1 ≤ d₁) (hd₂ : 1 ≤ d₂) (hd₃ : 1 ≤ d₃)
    (hd : d₁*d₂ = d) (hd₃d : d₃ ≤ d) (hM : 0 ≤ M) (hBY : 0 ≤ BY) :
    (1/d₁)*(M/d₂ + BY/d₃) * max 1 ((d₁^3*d₃^4/d^3)^(1/4 : ℝ)) ≤ M+BY := by
  have hd1 : 1 ≤ d := by rw [← hd]; exact one_le_mul_of_one_le_of_one_le hd₁ hd₂
  have hdp : 0 < d := by linarith
  have h1p : 0 < d₁ := by linarith
  have h2p : 0 < d₂ := by linarith
  have h3p : 0 < d₃ := by linarith
  have hd₁d : d₁ ≤ d := by nlinarith
  let t : ℝ := d₁^3*d₃^4/d^3
  let r : ℝ := t^(1/4 : ℝ)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hr : 0 ≤ r := Real.rpow_nonneg ht _
  have hr4 : r^4 = t := by
    dsimp [r]
    rw [← Real.rpow_mul_natCast ht]
    norm_num
  have htD : t ≤ d^4 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < d^3)).2
    calc d₁^3*d₃^4 ≤ d^3*d^4 := by gcongr
      _ = _ := by ring
  have ht13 : t ≤ (d₁*d₃)^4 := by
    dsimp [t]
    apply (div_le_iff₀ (by positivity : 0 < d^3)).2
    have hx : 1 ≤ d₁*d^3 := one_le_mul_of_one_le_of_one_le hd₁ (one_le_pow₀ hd1)
    nlinarith [mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ d₁^3*d₃^4)]
  have hrD : r ≤ d := (pow_le_pow_iff_left₀ hr hdp.le (by norm_num : (4:ℕ) ≠ 0)).1
    (by rw [hr4]; exact htD)
  have hr13 : r ≤ d₁*d₃ :=
    (pow_le_pow_iff_left₀ hr (by positivity : 0 ≤ d₁*d₃)
      (by norm_num : (4:ℕ) ≠ 0)).1 (by rw [hr4]; exact ht13)
  have hcD : max 1 r ≤ d := max_le hd1 hrD
  have hc13 : max 1 r ≤ d₁*d₃ := max_le (one_le_mul_of_one_le_of_one_le hd₁ hd₃) hr13
  have heq : (1/d₁)*(M/d₂ + BY/d₃) = M/d + BY/(d₁*d₃) := by
    rw [← hd]
    field_simp
  change (1/d₁)*(M/d₂ + BY/d₃) * max 1 r ≤ M+BY
  rw [heq]
  calc _ = M*(max 1 r/d) + BY*(max 1 r/(d₁*d₃)) := by ring
    _ ≤ M*1 + BY*1 := add_le_add
      (mul_le_mul_of_nonneg_left ((div_le_one hdp).2 hcD) hM)
      (mul_le_mul_of_nonneg_left ((div_le_one (mul_pos h1p h3p)).2 hc13) hBY)
    _ = M+BY := by ring

end
end DivisorProof


/-! ## Cutoff -/

/-! The single real gcd cutoff and its exact finite partition. -/
namespace DivisorProof
open Finset
open scoped BigOperators
noncomputable section

/-- The sole cutoff in equation (20). -/
def gcdCutoff (q : QuadraticScales) (ρ : ℝ) : ℝ :=
  (q.A*q.B)^(1/2 : ℝ) * q.mass^(-100*ρ)

theorem gcdCutoff_pos (q : QuadraticScales) {ρ : ℝ}
    (h : ∀ j, 1 ≤ q.size j) : 0 < gcdCutoff q ρ := by
  obtain ⟨hAB, hABQ⟩ := product_AB_le_mass q h
  unfold gcdCutoff
  exact mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (by linarith) _)

theorem gcdCutoff_le_sqrt_mass (q : QuadraticScales) {ρ : ℝ}
    (h : ∀ j, 1 ≤ q.size j) (hρ : 0 ≤ ρ) :
    gcdCutoff q ρ ≤ (q.A*q.B)^(1/2 : ℝ) ∧
    gcdCutoff q ρ ≤ q.mass^(1/2 : ℝ) := by
  obtain ⟨hAB, hABQ⟩ := product_AB_le_mass q h
  have hQ : 1 ≤ q.mass := hAB.trans hABQ
  have hc : q.mass^(-100*ρ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hQ (by linarith)
  have hcut : gcdCutoff q ρ ≤ (q.A*q.B)^(1/2 : ℝ) := by
    unfold gcdCutoff
    simpa using mul_le_mul_of_nonneg_left hc
      (Real.rpow_nonneg (by linarith : 0 ≤ q.A*q.B) (1/2 : ℝ))
  exact ⟨hcut, hcut.trans (Real.rpow_le_rpow (by linarith) hABQ (by norm_num))⟩

/-- Exhaustive disjoint splitting at a real cutoff, including empty ranges. -/
theorem one_cutoff_partition {V : Type*} [AddCommMonoid V]
    (s : Finset ℕ) (D : ℝ) (f : ℕ → V) :
    ∑ d ∈ s, f d =
      (∑ d ∈ s.filter (fun d : ℕ => (d : ℝ) ≤ D), f d) +
      ∑ d ∈ s.filter (fun d : ℕ => D < (d : ℝ)), f d := by
  classical
  simpa only [not_le] using (sum_filter_add_sum_filter_not s (fun d : ℕ => (d : ℝ) ≤ D) f).symm

/-- The two cutoff sets have no common index. -/
theorem one_cutoff_disjoint (s : Finset ℕ) (D : ℝ) :
    Disjoint (s.filter (fun d : ℕ => (d : ℝ) ≤ D))
      (s.filter (fun d : ℕ => D < (d : ℝ))) := by
  simp only [Finset.disjoint_left, mem_filter]
  intro d hd hd'
  exact (not_lt_of_ge hd.2) hd'.2

end
end DivisorProof


/-! ## Majorant -/

/-! The unchanged oriented majorant and its separated exponent losses. -/
namespace DivisorProof
noncomputable section

/-- The three literal terms in equation (4). -/
def E₀ (q : QuadraticScales) : ℝ := (q.mass*q.H^2)^(1/4 : ℝ)*q.A*q.B
def E₁ (q : QuadraticScales) : ℝ :=
  q.mass^(3/8 : ℝ)*q.H^(3/4 : ℝ)*q.A^(3/8 : ℝ)*q.B^(1/8 : ℝ)
def E₂ (q : QuadraticScales) : ℝ :=
  q.mass^(3/8 : ℝ)*q.H^(3/4 : ℝ)*(q.A*q.B)^(1/4 : ℝ)

theorem orientedMajorant_eq (q : QuadraticScales)
    (hQ : 0 ≤ q.mass) (hH : 0 ≤ q.H) :
    orientedQuadraticMajorant q = 2*E₀ q + E₁ q + E₂ q := by
  have hp : (q.mass*q.H^2)^(1/4 : ℝ) = q.mass^(1/4 : ℝ)*q.H^(1/2 : ℝ) := by
    rw [Real.mul_rpow hQ (sq_nonneg _), ← Real.rpow_natCast,
      ← Real.rpow_mul hH]
    norm_num
  have hc : (q.mass*q.H^2)^(1/4 : ℝ)*q.H^(1/4 : ℝ)*q.mass^(1/8 : ℝ) =
      q.mass^(3/8 : ℝ)*q.H^(3/4 : ℝ) := by
    rw [hp]
    calc _ = (q.mass^(1/4 : ℝ)*q.mass^(1/8 : ℝ))*
        (q.H^(1/2 : ℝ)*q.H^(1/4 : ℝ)) := by ring
      _ = _ := by
        rw [← Real.rpow_add_of_nonneg hQ (by norm_num) (by norm_num),
          ← Real.rpow_add_of_nonneg hH (by norm_num) (by norm_num)]
        norm_num
  unfold orientedQuadraticMajorant E₀ E₁ E₂
  calc _ = 2*((q.mass*q.H^2)^(1/4 : ℝ)*q.A*q.B) +
      ((q.mass*q.H^2)^(1/4 : ℝ)*q.H^(1/4 : ℝ)*q.mass^(1/8 : ℝ))*
      (q.A^(3/8 : ℝ)*q.B^(1/8 : ℝ)+(q.A*q.B)^(1/4 : ℝ)) := by ring
    _ = _ := by rw [hc]; ring

theorem orientedMajorant_nonneg (q : QuadraticScales)
    (hA : 0 ≤ q.A) (hB : 0 ≤ q.B) (hQ : 0 ≤ q.mass) (hH : 0 ≤ q.H) :
    0 ≤ orientedQuadraticMajorant q := by
  unfold orientedQuadraticMajorant
  positivity

/-- The scalar implication needed to pass from (9) to (10).
This is a comparison of numerical majorants, not a divisor-sum premise. -/
theorem separated_majorant_le {Q H E ε ρ : ℝ}
    (hQ : 1 ≤ Q) (hH : 1 ≤ H) (hE : 0 ≤ E) (hε : 0 ≤ ε)
    (hρε : 1000*ρ ≤ ε) :
    Q^(1000*ρ)*(E+H^2) ≤ (Q*H^2)^ε*E + Q^ε*H^2 := by
  have hpow : Q^(1000*ρ) ≤ Q^ε := Real.rpow_le_rpow_of_exponent_le hQ hρε
  have hQH : Q ≤ Q*H^2 := le_mul_of_one_le_right (by linarith) (one_le_pow₀ hH)
  have hpowH : Q^ε ≤ (Q*H^2)^ε := Real.rpow_le_rpow (by linarith) hQH hε
  calc _ = Q^(1000*ρ)*E + Q^(1000*ρ)*H^2 := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (hpow.trans hpowH) hE)
      (mul_le_mul_of_nonneg_right hpow (sq_nonneg _))

theorem exponent_226_le_1000 {Q ρ : ℝ} (hQ : 1 ≤ Q) (hρ : 0 ≤ ρ) :
    Q^(226*ρ) ≤ Q^(1000*ρ) :=
  Real.rpow_le_rpow_of_exponent_le hQ (by linarith)

/-- Exact multiplication of the final normalized loss by the norming cost. -/
theorem final_loss_identity {Q ρ : ℝ} (hQ : 0 < Q) :
    (Q^ρ)^6 * Q^(220*ρ) = Q^(226*ρ) := by
  rw [← Real.rpow_mul_natCast hQ.le, ← Real.rpow_add hQ]
  congr 1
  norm_num
  ring

end
end DivisorProof


/-! ## Summation -/

/-! Elementary finite summation bounds used at the single gcd cutoff. -/
namespace DivisorProof
open Finset MeasureTheory Set
open scoped BigOperators
noncomputable section

/-- Equation (12) with arbitrary nonnegative real upper scales. -/
theorem averaged_sqrt_gcd_le {L U : ℝ} (hL : 0 ≤ L) (hU : 0 ≤ U)
    (c : ℕ) (hc : c ≠ 0) :
    ∑ l ∈ Finset.Icc 1 ⌊L⌋₊, ∑ k ∈ Finset.Icc 1 ⌊U⌋₊,
      Real.sqrt (Nat.gcd (l*k) c) ≤ L*U*(c.divisors.card : ℝ)^2 := by
  calc _ ≤ (⌊L⌋₊ : ℝ)*⌊U⌋₊*(c.divisors.card : ℝ)^2 :=
          sum_sum_sqrt_gcd_le ⌊L⌋₊ ⌊U⌋₊ c hc
    _ ≤ _ := by
      gcongr
      · exact Nat.floor_le hL
      · exact Nat.floor_le hU

private theorem sum_Ioc_rpow_eq (j N : ℕ) (p : ℝ) :
    (∑ n ∈ Finset.Ioc j N, (n : ℝ)^p) =
    ∑ n ∈ Finset.Ico j N, ((n+1 : ℕ) : ℝ)^p := by
  symm
  apply Finset.sum_bij (fun n _ => n+1)
  · intro n hn
    simp only [Finset.mem_Ico, Finset.mem_Ioc] at hn ⊢
    omega
  · intro n hn m hm hnm
    omega
  · intro m hm
    refine ⟨m-1, ?_, ?_⟩
    · simp only [Finset.mem_Ico, Finset.mem_Ioc] at hm ⊢
      omega
    · simp only [Finset.mem_Ioc] at hm
      omega
  · intro n hn
    rfl

/-- Integral comparison with the sharp constant used in (13). -/
theorem tail_rpow_bound_nat (j N : ℕ) (hj : 1 ≤ j) :
    ∑ n ∈ Finset.Icc j N, (n : ℝ)^(-5/2 : ℝ) ≤
      (5/3 : ℝ)*(j : ℝ)^(-3/2 : ℝ) := by
  by_cases hjN : j ≤ N
  · rw [← Finset.add_sum_Ioc_eq_sum_Icc hjN, sum_Ioc_rpow_eq]
    have hjp : (0 : ℝ) < j := by exact_mod_cast hj
    have hanti : AntitoneOn (fun x : ℝ => x^(-5/2 : ℝ)) (Set.Icc (j : ℝ) N) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (hjp.trans_le hx.1) hxy (by norm_num)
    have hint := hanti.sum_Ico_le_integral
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-5/2 : ℝ) < -1) hjp)
      (fun t ht => Real.rpow_nonneg (hjp.trans ht).le _)
    have heval : (∫ t : ℝ in Set.Ioi (j : ℝ), t^(-5/2 : ℝ)) =
        (2/3 : ℝ)*(j : ℝ)^(-3/2 : ℝ) := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-5/2 : ℝ) < -1) hjp]
      norm_num
      ring
    have hp : (j : ℝ)^(-5/2 : ℝ) ≤ (j : ℝ)^(-3/2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by norm_num)
    rw [heval] at hint
    linarith
  · rw [Finset.Icc_eq_empty_of_lt (lt_of_not_ge hjN), Finset.sum_empty]
    positivity

/-- Lemma 3.3 (13), in the finite form actually used in §5.2.
The real cutoff may lie below one, and the large-gcd range may be empty. -/
theorem tail_rpow_bound {D : ℝ} (hD : 0 < D) (N : ℕ) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => D < (n : ℝ)),
      (n : ℝ)^(-5/2 : ℝ) ≤ (5/3 : ℝ)*D^(-3/2 : ℝ) := by
  let j : ℕ := ⌊D⌋₊+1
  have hj : 1 ≤ j := by omega
  have hDj : D ≤ (j : ℝ) := by
    dsimp [j]
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one D).le
  have hset : (Finset.Icc 1 N).filter (fun n : ℕ => D < (n : ℝ)) =
      Finset.Icc j N := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [← Nat.floor_lt hD.le]
    dsimp [j]
    omega
  rw [hset]
  calc _ ≤ (5/3 : ℝ)*(j : ℝ)^(-3/2 : ℝ) := tail_rpow_bound_nat j N hj
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hD hDj (by norm_num)) (by norm_num)

private theorem tail_rpow_bound_finset {D : ℝ} (hD : 0 < D) (s : Finset ℕ) :
    ∑ n ∈ s, (if D < (n : ℝ) then (n : ℝ)^(-5/2 : ℝ) else 0) ≤
      (5/3 : ℝ)*D^(-3/2 : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  have hsub : s.filter (fun n : ℕ => D < (n : ℝ)) ⊆
      (Finset.Icc 1 (s.sup id)).filter (fun n : ℕ => D < (n : ℝ)) := by
    intro n hn
    obtain ⟨hns, hnD⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, Finset.le_sup (f := id) hns⟩, hnD⟩
    have hnp : (0 : ℝ) < n := hD.trans hnD
    exact Nat.succ_le_of_lt (by exact_mod_cast hnp)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) (-5/2 : ℝ))).trans
      (tail_rpow_bound hD (s.sup id))

/-- The infinite tail in (13) is summable; it is not interpreted via an
undefined or divergent sum. -/
theorem tail_rpow_summable {D : ℝ} (hD : 0 < D) :
    Summable (fun n : ℕ => if D < (n : ℝ) then (n : ℝ)^(-5/2 : ℝ) else 0) := by
  apply summable_of_sum_le (c := (5/3 : ℝ)*D^(-3/2 : ℝ))
  · intro n
    change 0 ≤ if D < (n : ℝ) then (n : ℝ)^(-5/2 : ℝ) else 0
    split_ifs <;> positivity
  · exact tail_rpow_bound_finset hD

/-- The full infinite version of Lemma 3.3 (13), for every positive real cutoff. -/
theorem tail_rpow_tsum_le {D : ℝ} (hD : 0 < D) :
    (∑' n : ℕ, if D < (n : ℝ) then (n : ℝ)^(-5/2 : ℝ) else 0) ≤
      (5/3 : ℝ)*D^(-3/2 : ℝ) :=
  (tail_rpow_summable hD).tsum_le_of_sum_le (tail_rpow_bound_finset hD)

end
end DivisorProof


/-! ## Asymptotics -/

/-! The unconditional scalar asymptotic statements used at the end of §8.
They do not assert a bound on the analytic source error. -/
namespace DivisorProof
open Filter Asymptotics
open scoped Topology
noncomputable section

/-- Every fixed logarithmic power is negligible relative to any positive power. -/
theorem log_pow_isLittleO {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    (fun T : ℝ => (Real.log T)^k) =o[atTop] (fun T : ℝ => T^ℓ) := by
  simpa only [Real.rpow_natCast] using
    isLittleO_log_rpow_rpow_atTop (k : ℝ) hℓ

/-- The last displayed scalar power in §8 is `o(T)`. -/
theorem saved_power_isLittleO {γ : ℝ} (hγ : 0 < γ) :
    (fun T : ℝ => T^(1-γ/2)) =o[atTop] (fun T : ℝ => T) := by
  apply Asymptotics.isLittleO_of_tendsto'
    ((eventually_gt_atTop (0 : ℝ)).mono (fun T hT hz => (ne_of_gt hT hz).elim))
  have ht : Tendsto (fun T : ℝ => T^(-(γ/2))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith : 0 < γ/2)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [← Real.rpow_sub_one hT.ne']
  congr 1
  ring

/-- A positive source gap follows on the full triangular range in the PDF. -/
theorem source_saved_power_isLittleO {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hrange : 3*a+5*b < 2) :
    (fun T : ℝ => T^(1-sourceGap a b/2)) =o[atTop] (fun T : ℝ => T) :=
  saved_power_isLittleO (sourceGap_pos ha hab hrange)

end
end DivisorProof


/-! ## Scalar Transfer -/

/-!
Algebraic transfer of the finer, unsymmetrised BBLR block errors.
No analytic bound for a divisor sum or for a moment is asserted here.
-/

namespace DivisorProof

export Sechstmoment (rectangularQuadraticMajorant rectangularExpandedMajorant
  rectangular_oriented_coefficient_le rectangular_small_d_coefficient_le
  rectangular_quadratic_majorant_expand rectangular_H0_back_transfer
  rectangular_endpoint_coefficient_le rectangular_poisson_back_transfer
  rectangular_source_majorant_le)

/-- The complete scalar majorant transfer from §8.2, retaining the `H²` term.
All hypotheses are numerical scale relations; no divisor estimate is a premise. -/
theorem reconstructed_majorant_le (q : QuadraticScales) {X T K : ℝ}
    (hA : 0 < q.A) (hB : 0 < q.B) (hX : 0 < X) (hH : 0 < q.H)
    (hT : 0 < T) (hK : 0 < K)
    (hmass : q.mass = q.A*q.B*X^2)
    (hH0 : q.H ≤ K*(q.A*q.B)^(1/2 : ℝ)*X/T) :
    T/((q.A*q.B)^(1/2 : ℝ)*X)*(orientedQuadraticMajorant q+q.H^2) ≤
      2*(K^(1/2 : ℝ)*T^(1/2 : ℝ)*(q.A*q.B) +
        K^(3/4 : ℝ)*T^(1/4 : ℝ)*(q.A*q.B)^(3/8 : ℝ)*
          (max q.A q.B)^(1/4 : ℝ)*X^(1/2 : ℝ)) +
      K^2*(q.A*q.B)^(1/2 : ℝ)*X/T := by
  have hF : 0 ≤ T/((q.A*q.B)^(1/2 : ℝ)*X) := by positivity
  have hmaj := rectangular_source_majorant_le q hA.le hB.le hX.le hH.le hmass
  have hblock := rectangular_H0_back_transfer hT hA hB hX hH hK hH0
  have hpois := rectangular_poisson_back_transfer hT (mul_pos hA hB) hX hH.le hK hH0
  calc _ ≤ T/((q.A*q.B)^(1/2 : ℝ)*X)*
        (2*rectangularQuadraticMajorant q.A q.B X q.H+q.H^2) :=
      mul_le_mul_of_nonneg_left (add_le_add hmaj le_rfl) hF
    _ = 2*(T/((q.A*q.B)^(1/2 : ℝ)*X)*
        rectangularQuadraticMajorant q.A q.B X q.H) +
        T/((q.A*q.B)^(1/2 : ℝ)*X)*q.H^2 := by ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hblock (by norm_num)) hpois

/-- A polynomial scale bound gives exactly the `T^(r ε)` loss in (34). -/
theorem polynomial_mass_loss {mass D T r ε : ℝ}
    (hmass : 0 ≤ mass) (hD : 0 ≤ D) (hT : 0 ≤ T) (hε : 0 ≤ ε)
    (hgrowth : mass ≤ D*T^r) : mass^ε ≤ D^ε*T^(r*ε) :=
  Sechstmoment.rectangular_source_mass_power_le hmass hD hT hε hgrowth

end DivisorProof


/-! ## Specification -/

/-!
The requested final statement, kept separate from the proved lemmas.
`QuantifiedDivisorBound` and `SeparatedDivisorBound` specify the PDF's goals.
Their proofs from the proved Estermann estimate and the Watt input are supplied in
MainFromPrimitives near the end of this file.
-/
namespace DivisorProof
noncomputable section

/-- The literal conclusion of Theorem 1.2, with all quantifiers in the stated order. -/
def QuantifiedDivisorBound : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ/(1000*(1+δ)) →
  ∀ K : ℝ, 1 ≤ K → ∀ bounds : ℕ → ℝ, (∀ j, 0 ≤ bounds j) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ), QuadraticAdmissible ρ δ K bounds q α β W →
      ∀ positive : Bool, ‖signedQuadraticDiscrepancy positive q α β W‖ ≤
        C*q.mass^(1000*ρ)*(orientedQuadraticMajorant q+q.H^2)

/-- The literal separated-exponent contract of Corollary 1.3.
This intentionally differs from `BBLRv1OrientedInput` in the original repository:
the admissibility exponent here is `inputExponent ε δ`, not `ε`. -/
abbrev SeparatedDivisorBound : Prop := Sechstmoment.Source.SeparatedQuadraticInput

end
end DivisorProof
