import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Sechstmoment.Certificate.Kernels.Unbalanced.BoxPolynomial
import Sechstmoment.Certificate.Kernels.Unbalanced.InclusionExclusion

/-!
# Binomial expansion of the eight unbalanced-denominator masks

All integrals use the genuine two-dimensional slice measure of (5.7).
The masks, their signs, and the nonpositive-length cutoff are inherited from
`BoxInclusionExclusion`, hence use exactly the integer evaluator's convention.
-/

namespace Sechstmoment
open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 0

private theorem sliceIntegral_finsetSum {ι : Type*} (H : ℝ) (s : Finset ι)
    (f : ι → (Fin 2 → ℝ) → ℝ) (hf : ∀ i, Continuous (f i)) :
    (∫ r, (simplexSlice H).indicator (fun r => ∑ i ∈ s, f i r) r) =
      ∑ i ∈ s, ∫ r, (simplexSlice H).indicator (f i) r := by
  classical
  have he (r : Fin 2 → ℝ) :
      (simplexSlice H).indicator (fun r => ∑ i ∈ s, f i r) r =
        ∑ i ∈ s, (simplexSlice H).indicator (f i) r := by
    by_cases hr : r ∈ simplexSlice H <;> simp [hr]
  simp_rw [he]
  rw [integral_finsetSum]
  intro i _
  exact simplexSlice_indicator_integrable H (f i) (hf i)

private theorem sliceIntegral_const_mul (H c : ℝ) (f : (Fin 2 → ℝ) → ℝ) :
    (∫ r, (simplexSlice H).indicator (fun r => c*f r) r) =
      c * ∫ r, (simplexSlice H).indicator f r := by
  classical
  have he (r : Fin 2 → ℝ) :
      (simplexSlice H).indicator (fun r => c*f r) r =
        c*(simplexSlice H).indicator f r := by
    by_cases hr : r ∈ simplexSlice H <;> simp [hr]
  simp_rw [he]
  rw [integral_const_mul]

/-- The index `d` is the power of the selected cap. -/
theorem shift_power_binomial (x a : ℝ) (e : ℕ) :
    (x+a)^e = ∑ d ∈ Finset.range (e+1),
      (Nat.choose e d : ℝ)*a^d*x^(e-d) := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem translatedSimplexMonomial_expand (H a b c : ℝ) (e₁ e₂ e₃ : ℕ)
    (r : Fin 2 → ℝ) :
    (r 0+a)^e₁*(r 1+b)^e₂*(H-r 0-r 1+c)^e₃ =
      ∑ d₁ ∈ Finset.range (e₁+1), ∑ d₂ ∈ Finset.range (e₂+1),
        ∑ d₃ ∈ Finset.range (e₃+1),
          ((Nat.choose e₁ d₁ : ℝ)*(Nat.choose e₂ d₂ : ℝ)*(Nat.choose e₃ d₃ : ℝ)*
            a^d₁*b^d₂*c^d₃) *
          (r 0^(e₁-d₁)*r 1^(e₂-d₂)*(H-r 0-r 1)^(e₃-d₃)) := by
  rw [shift_power_binomial, shift_power_binomial, shift_power_binomial]
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d₁ _
  apply Finset.sum_congr rfl
  intro d₂ _
  apply Finset.sum_congr rfl
  intro d₃ _
  ring

/-- The translated exponent includes the two-dimensional slice measure. -/
def translatedSimplexExponent (e₁ e₂ e₃ d₁ d₂ d₃ : ℕ) : ℕ :=
  e₁+e₂+e₃+2-d₁-d₂-d₃

theorem translatedSimplexExponent_eq {e₁ e₂ e₃ d₁ d₂ d₃ : ℕ}
    (h₁ : d₁ ≤ e₁) (h₂ : d₂ ≤ e₂) (h₃ : d₃ ≤ e₃) :
    translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃ =
      (e₁-d₁)+(e₂-d₂)+(e₃-d₃)+2 := by
  unfold translatedSimplexExponent
  omega

/-- The exact result of translating a single simplex monomial. -/
noncomputable def translatedSimplexMonomialValue (H a b c : ℝ) (e₁ e₂ e₃ : ℕ) : ℝ :=
  ∑ d₁ ∈ Finset.range (e₁+1), ∑ d₂ ∈ Finset.range (e₂+1),
    ∑ d₃ ∈ Finset.range (e₃+1),
      (Nat.factorial e₁ : ℝ)*Nat.factorial e₂*Nat.factorial e₃ *
        a^d₁*b^d₂*c^d₃*H^(translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃) /
        ((Nat.factorial d₁ : ℝ)*Nat.factorial d₂*Nat.factorial d₃*
          Nat.factorial (translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃))

private theorem binomial_simplex_cancellation (H a b c : ℝ)
    {e₁ e₂ e₃ d₁ d₂ d₃ : ℕ}
    (h₁ : d₁ ≤ e₁) (h₂ : d₂ ≤ e₂) (h₃ : d₃ ≤ e₃) :
    ((Nat.choose e₁ d₁ : ℝ)*(Nat.choose e₂ d₂ : ℝ)*(Nat.choose e₃ d₃ : ℝ)*
        a^d₁*b^d₂*c^d₃) *
      ((Nat.factorial (e₁-d₁) : ℝ)*Nat.factorial (e₂-d₂)*Nat.factorial (e₃-d₃) /
        Nat.factorial ((e₁-d₁)+(e₂-d₂)+(e₃-d₃)+2) *
        H^((e₁-d₁)+(e₂-d₂)+(e₃-d₃)+2)) =
    (Nat.factorial e₁ : ℝ)*Nat.factorial e₂*Nat.factorial e₃ *
        a^d₁*b^d₂*c^d₃*H^(translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃) /
        ((Nat.factorial d₁ : ℝ)*Nat.factorial d₂*Nat.factorial d₃*
          Nat.factorial (translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃)) := by
  rw [translatedSimplexExponent_eq h₁ h₂ h₃,
    Nat.cast_choose ℝ h₁, Nat.cast_choose ℝ h₂, Nat.cast_choose ℝ h₃]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d₁),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d₂),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d₃),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (e₁-d₁)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (e₂-d₂)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (e₃-d₃)),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero ((e₁-d₁)+(e₂-d₂)+(e₃-d₃)+2))]

theorem translatedSimplexMonomial_integral_nonneg {H : ℝ} (hH : 0 ≤ H)
    (a b c : ℝ) (e₁ e₂ e₃ : ℕ) :
    (∫ r, (simplexSlice H).indicator
      (fun r => (r 0+a)^e₁*(r 1+b)^e₂*(H-r 0-r 1+c)^e₃) r) =
      translatedSimplexMonomialValue H a b c e₁ e₂ e₃ := by
  simp_rw [translatedSimplexMonomial_expand]
  rw [sliceIntegral_finsetSum H _ _ (by intro d₁; fun_prop)]
  unfold translatedSimplexMonomialValue
  apply Finset.sum_congr rfl
  intro d₁ hd₁
  rw [sliceIntegral_finsetSum H _ _ (by intro d₂; fun_prop)]
  apply Finset.sum_congr rfl
  intro d₂ hd₂
  rw [sliceIntegral_finsetSum H _ _ (by intro d₃; fun_prop)]
  apply Finset.sum_congr rfl
  intro d₃ hd₃
  rw [sliceIntegral_const_mul, simplexSlice_monomial_integral hH]
  exact binomial_simplex_cancellation H a b c
    (Nat.le_of_lt_succ (Finset.mem_range.mp hd₁))
    (Nat.le_of_lt_succ (Finset.mem_range.mp hd₂))
    (Nat.le_of_lt_succ (Finset.mem_range.mp hd₃))

/-- The general translated moment with the exact empty/singleton cutoff. -/
theorem translatedSimplexMonomial_integral (H a b c : ℝ) (e₁ e₂ e₃ : ℕ) :
    (∫ r, (simplexSlice H).indicator
      (fun r => (r 0+a)^e₁*(r 1+b)^e₂*(H-r 0-r 1+c)^e₃) r) =
      if H ≤ 0 then 0 else translatedSimplexMonomialValue H a b c e₁ e₂ e₃ := by
  by_cases hH : H ≤ 0
  · rw [ite_eq_left hH, simplexSlice_integral_zero_of_nonpos hH]
  · rw [ite_eq_right hH]
    exact translatedSimplexMonomial_integral_nonneg (le_of_lt (lt_of_not_ge hH)) a b c e₁ e₂ e₃

/-- The scalar shift for a selected mask coordinate. -/
def minusMaskCap (a : ℝ) (mask : Fin 8) (i : ℕ) : ℝ :=
  if Finite.bit mask.val i then a else 0

/-- A nonselected coordinate contributes only `d=0`, exactly as in `momentTerms`. -/
theorem minusMaskCap_sum (a : ℝ) (mask : Fin 8) (i e : ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ Finset.range (e+1), (minusMaskCap a mask i)^d*f d) =
      ∑ d ∈ Finset.range (if Finite.bit mask.val i then e+1 else 1), a^d*f d := by
  cases hb : Finite.bit mask.val i
  · simp only [minusMaskCap, hb, Bool.coe_false, ite_false, Finset.sum_range_one,
      pow_zero, one_mul]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro d _ hd
      rw [zero_pow hd, zero_mul]
    · intro hzero
      exact False.elim (hzero (Finset.mem_range.mpr (Nat.zero_lt_succ e)))
  · simp [minusMaskCap, hb]

theorem minusMaskCap_triple_sum (a b c : ℝ) (mask : Fin 8) (e₁ e₂ e₃ : ℕ)
    (f : ℕ → ℕ → ℕ → ℝ) :
    (∑ d₁ ∈ Finset.range (e₁+1), ∑ d₂ ∈ Finset.range (e₂+1),
      ∑ d₃ ∈ Finset.range (e₃+1),
        (minusMaskCap a mask 0)^d₁*(minusMaskCap b mask 1)^d₂*
          (minusMaskCap c mask 2)^d₃*f d₁ d₂ d₃) =
      ∑ d₁ ∈ Finset.range (if Finite.bit mask.val 0 then e₁+1 else 1),
        ∑ d₂ ∈ Finset.range (if Finite.bit mask.val 1 then e₂+1 else 1),
          ∑ d₃ ∈ Finset.range (if Finite.bit mask.val 2 then e₃+1 else 1),
            a^d₁*b^d₂*c^d₃*f d₁ d₂ d₃ := by
  calc
    _ = ∑ d₁ ∈ Finset.range (e₁+1), (minusMaskCap a mask 0)^d₁*
        (∑ d₂ ∈ Finset.range (e₂+1), (minusMaskCap b mask 1)^d₂*
          (∑ d₃ ∈ Finset.range (e₃+1), (minusMaskCap c mask 2)^d₃*f d₁ d₂ d₃)) := by
      simp only [Finset.mul_sum, mul_assoc]
    _ = ∑ d₁ ∈ Finset.range (if Finite.bit mask.val 0 then e₁+1 else 1), a^d₁*
        (∑ d₂ ∈ Finset.range (if Finite.bit mask.val 1 then e₂+1 else 1), b^d₂*
          (∑ d₃ ∈ Finset.range (if Finite.bit mask.val 2 then e₃+1 else 1),
            c^d₃*f d₁ d₂ d₃)) := by
      simp_rw [minusMaskCap_sum]
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

theorem simplexUpperMask_monomial_integral {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ)
    (mask : Fin 8) (e₁ e₂ e₃ : ℕ) :
    (∫ r, (simplexUpperMask a b c H mask).indicator
      (fun r => r 0^e₁*r 1^e₂*(H-r 0-r 1)^e₃) r) =
      if H-simplexMaskShift a b c mask ≤ 0 then 0 else
        translatedSimplexMonomialValue (H-simplexMaskShift a b c mask)
          (minusMaskCap a mask 0) (minusMaskCap b mask 1) (minusMaskCap c mask 2)
          e₁ e₂ e₃ := by
  rw [simplexUpperMask_integral_simplex ha hb hc H mask]
  have he (r : Fin 2 → ℝ) :
      (simplexMaskTranslate a b mask r) 0^e₁*(simplexMaskTranslate a b mask r) 1^e₂*
        (H-(simplexMaskTranslate a b mask r) 0-(simplexMaskTranslate a b mask r) 1)^e₃ =
      (r 0+minusMaskCap a mask 0)^e₁*(r 1+minusMaskCap b mask 1)^e₂*
        ((H-simplexMaskShift a b c mask)-r 0-r 1+minusMaskCap c mask 2)^e₃ := by
    simp only [simplexMaskTranslate, minusMaskCap, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hs : H-(r 0+(if Finite.bit mask.val 0 then a else 0))-
        (r 1+(if Finite.bit mask.val 1 then b else 0)) =
      (H-simplexMaskShift a b c mask)-r 0-r 1+
        (if Finite.bit mask.val 2 then c else 0) := by
      unfold simplexMaskShift
      ring
    rw [hs]
  simp_rw [he]
  exact translatedSimplexMonomial_integral _ _ _ _ _ _ _

/-- Eight-mask monomial evaluator on the truncated slice. -/
theorem boundedSimplexSlice_monomial_integral {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ)
    (e₁ e₂ e₃ : ℕ) :
    (∫ r, (boundedSimplexSlice a b c H).indicator
      (fun r => r 0^e₁*r 1^e₂*(H-r 0-r 1)^e₃) r) =
      ∑ mask : Fin 8, simplexMaskSign mask *
        (if H-simplexMaskShift a b c mask ≤ 0 then 0 else
          translatedSimplexMonomialValue (H-simplexMaskShift a b c mask)
            (minusMaskCap a mask 0) (minusMaskCap b mask 1) (minusMaskCap c mask 2)
            e₁ e₂ e₃) := by
  rw [boundedSimplexSlice_integral_of_continuous a b c H _ (by fun_prop)]
  simp_rw [simplexUpperMask_monomial_integral ha hb hc]

/-- Cancellation of the factorials from the box-moment multinomial coefficient. -/
theorem translatedSimplexMonomialValue_weighted (H a b c : ℝ)
    (k e₁ e₂ e₃ : ℕ) :
    ((Nat.factorial k : ℝ) /
      ((2 : ℝ)^k*Nat.factorial e₁*Nat.factorial e₂*Nat.factorial e₃)) *
      translatedSimplexMonomialValue H a b c e₁ e₂ e₃ =
    ((Nat.factorial k : ℝ)/(2 : ℝ)^k) *
      ∑ d₁ ∈ Finset.range (e₁+1), ∑ d₂ ∈ Finset.range (e₂+1),
        ∑ d₃ ∈ Finset.range (e₃+1),
          a^d₁*b^d₂*c^d₃*H^(translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃) /
            ((Nat.factorial d₁ : ℝ)*Nat.factorial d₂*Nat.factorial d₃*
              Nat.factorial (translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃)) := by
  unfold translatedSimplexMonomialValue
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d₁ _
  apply Finset.sum_congr rfl
  intro d₂ _
  apply Finset.sum_congr rfl
  intro d₃ _
  have hfac (n : ℕ) : (Nat.factorial n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  field_simp [hfac, pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)]

theorem translatedSimplexExponent_even {k l₁ l₂ l₃ : ℕ}
    (hl : l₁+l₂+l₃ = k) (d₁ d₂ d₃ : ℕ) :
    translatedSimplexExponent (2*l₁+1) (2*l₂+1) (2*l₃+1) d₁ d₂ d₃ =
      2*k+5-d₁-d₂-d₃ := by
  unfold translatedSimplexExponent
  omega

/-- The three exponent ranges in precisely the evaluator's bit convention. -/
noncomputable def minusMaskMonomialSum (H a b c : ℝ) (mask : Fin 8)
    (e₁ e₂ e₃ : ℕ) : ℝ :=
  ∑ d₁ ∈ Finset.range (if Finite.bit mask.val 0 then e₁+1 else 1),
    ∑ d₂ ∈ Finset.range (if Finite.bit mask.val 1 then e₂+1 else 1),
      ∑ d₃ ∈ Finset.range (if Finite.bit mask.val 2 then e₃+1 else 1),
        a^d₁*b^d₂*c^d₃*H^(translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃) /
          ((Nat.factorial d₁ : ℝ)*Nat.factorial d₂*Nat.factorial d₃*
            Nat.factorial (translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃))

theorem translatedSimplexMonomialValue_weighted_mask (H a b c : ℝ)
    (mask : Fin 8) (k e₁ e₂ e₃ : ℕ) :
    ((Nat.factorial k : ℝ) /
      ((2 : ℝ)^k*Nat.factorial e₁*Nat.factorial e₂*Nat.factorial e₃)) *
      translatedSimplexMonomialValue H
        (minusMaskCap a mask 0) (minusMaskCap b mask 1) (minusMaskCap c mask 2)
        e₁ e₂ e₃ =
    ((Nat.factorial k : ℝ)/(2 : ℝ)^k) *
      minusMaskMonomialSum H a b c mask e₁ e₂ e₃ := by
  rw [translatedSimplexMonomialValue_weighted]
  congr 1
  unfold minusMaskMonomialSum
  simpa only [div_eq_mul_inv, mul_assoc] using
    minusMaskCap_triple_sum a b c mask e₁ e₂ e₃
      (fun d₁ d₂ d₃ => H^(translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃) /
        ((Nat.factorial d₁ : ℝ)*Nat.factorial d₂*Nat.factorial d₃*
          Nat.factorial (translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃)))

theorem simplexUpperMask_weighted_monomial_integral {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ) (mask : Fin 8)
    (k e₁ e₂ e₃ : ℕ) :
    ((Nat.factorial k : ℝ) /
      ((2 : ℝ)^k*Nat.factorial e₁*Nat.factorial e₂*Nat.factorial e₃)) *
      (∫ r, (simplexUpperMask a b c H mask).indicator
        (fun r => r 0^e₁*r 1^e₂*(H-r 0-r 1)^e₃) r) =
      if H-simplexMaskShift a b c mask ≤ 0 then 0 else
        ((Nat.factorial k : ℝ)/(2 : ℝ)^k) *
          minusMaskMonomialSum (H-simplexMaskShift a b c mask) a b c mask e₁ e₂ e₃ := by
  rw [simplexUpperMask_monomial_integral ha hb hc]
  by_cases hh : H-simplexMaskShift a b c mask ≤ 0
  · simp only [ite_eq_left hh, mul_zero]
  · simp only [ite_eq_right hh]
    rw [translatedSimplexMonomialValue_weighted_mask]

/-- The exact factorial coefficient for an even box moment, in `momentTerms` ranges. -/
theorem simplexUpperMask_evenMonomial_integral {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ) (mask : Fin 8)
    (m l₁ l₂ l₃ : ℕ) (hl : l₁+l₂+l₃ = m) :
    ((Nat.factorial (2*m) : ℝ) /
      ((2 : ℝ)^(2*m)*Nat.factorial (2*l₁+1)*Nat.factorial (2*l₂+1)*
        Nat.factorial (2*l₃+1))) *
      (∫ r, (simplexUpperMask a b c H mask).indicator
        (fun r => r 0^(2*l₁+1)*r 1^(2*l₂+1)*(H-r 0-r 1)^(2*l₃+1)) r) =
      if H-simplexMaskShift a b c mask ≤ 0 then 0 else
        ∑ d₁ ∈ Finset.range (if Finite.bit mask.val 0 then 2*l₁+2 else 1),
          ∑ d₂ ∈ Finset.range (if Finite.bit mask.val 1 then 2*l₂+2 else 1),
            ∑ d₃ ∈ Finset.range (if Finite.bit mask.val 2 then 2*l₃+2 else 1),
              (Nat.factorial (2*m) : ℝ)*a^d₁*b^d₂*c^d₃*
                (H-simplexMaskShift a b c mask)^(2*m+5-d₁-d₂-d₃) /
                  ((2 : ℝ)^(2*m)*(Nat.factorial d₁ : ℝ)*Nat.factorial d₂*
                    Nat.factorial d₃*Nat.factorial (2*m+5-d₁-d₂-d₃)) := by
  rw [simplexUpperMask_weighted_monomial_integral ha hb hc]
  by_cases hh : H-simplexMaskShift a b c mask ≤ 0
  · simp only [ite_eq_left hh]
  · simp only [ite_eq_right hh]
    unfold minusMaskMonomialSum
    simp_rw [translatedSimplexExponent_even hl, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d₁ _
    apply Finset.sum_congr rfl
    intro d₂ _
    apply Finset.sum_congr rfl
    intro d₃ _
    ring

private theorem upperMaskIntegral_finsetSum {ι : Type*} (a b c H : ℝ) (mask : Fin 8)
    (s : Finset ι) (f : ι → (Fin 2 → ℝ) → ℝ) (hf : ∀ i, Continuous (f i)) :
    (∫ r, (simplexUpperMask a b c H mask).indicator (fun r => ∑ i ∈ s, f i r) r) =
      ∑ i ∈ s, ∫ r, (simplexUpperMask a b c H mask).indicator (f i) r := by
  classical
  have he (r : Fin 2 → ℝ) :
      (simplexUpperMask a b c H mask).indicator (fun r => ∑ i ∈ s, f i r) r =
        ∑ i ∈ s, (simplexUpperMask a b c H mask).indicator (f i) r := by
    by_cases hr : r ∈ simplexUpperMask a b c H mask <;> simp [hr]
  simp_rw [he]
  rw [integral_finsetSum]
  intro i _
  exact simplexUpperMask_indicator_integrable a b c H mask (f i) (hf i)

private theorem upperMaskIntegral_const_mul (a b c H : ℝ) (mask : Fin 8)
    (coef : ℝ) (f : (Fin 2 → ℝ) → ℝ) :
    (∫ r, (simplexUpperMask a b c H mask).indicator (fun r => coef*f r) r) =
      coef * ∫ r, (simplexUpperMask a b c H mask).indicator f r := by
  classical
  have he (r : Fin 2 → ℝ) :
      (simplexUpperMask a b c H mask).indicator (fun r => coef*f r) r =
        coef*(simplexUpperMask a b c H mask).indicator f r := by
    by_cases hr : r ∈ simplexUpperMask a b c H mask <;> simp [hr]
  simp_rw [he]
  rw [integral_const_mul]

private theorem upperMaskIntegral_div_const (a b c H : ℝ) (mask : Fin 8)
    (coef : ℝ) (f : (Fin 2 → ℝ) → ℝ) :
    (∫ r, (simplexUpperMask a b c H mask).indicator (fun r => f r/coef) r) =
      (∫ r, (simplexUpperMask a b c H mask).indicator f r)/coef := by
  simp only [div_eq_mul_inv, mul_comm _ coef⁻¹]
  exact upperMaskIntegral_const_mul a b c H mask coef⁻¹ f

/-- The full translated even moment, retaining the three `Fin (m+1)` indices. -/
noncomputable def minusMaskEvenMomentValue (m : ℕ) (mask : Fin 8) (a b c HH : ℝ) : ℝ :=
  (Nat.factorial (2*m) : ℝ)/(2 : ℝ)^(2*m) *
    ∑ l₁ : Fin (m+1), ∑ l₂ : Fin (m+1), ∑ l₃ : Fin (m+1),
      if l₁.val+l₂.val+l₃.val = m then
        translatedSimplexMonomialValue HH
          (minusMaskCap a mask 0) (minusMaskCap b mask 1) (minusMaskCap c mask 2)
          (2*l₁.val+1) (2*l₂.val+1) (2*l₃.val+1) /
          ((Nat.factorial (2*l₁.val+1) : ℝ)*Nat.factorial (2*l₂.val+1)*
            Nat.factorial (2*l₃.val+1)) else 0

/-- The actual box even moment on one inclusion–exclusion mask. -/
theorem simplexUpperMask_minusBoxEvenMoment_integral {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ) (mask : Fin 8) (m : ℕ) :
    (∫ r, (simplexUpperMask a b c H mask).indicator
      (fun r => minusBoxEvenMoment m (r 0) (r 1) (H-r 0-r 1)) r) =
      if H-simplexMaskShift a b c mask ≤ 0 then 0 else
        minusMaskEvenMomentValue m mask a b c (H-simplexMaskShift a b c mask) := by
  by_cases hh : H-simplexMaskShift a b c mask ≤ 0
  · rw [ite_eq_left hh, simplexUpperMask_integral_simplex ha hb hc]
    exact simplexSlice_integral_zero_of_nonpos hh _
  · simp only [ite_eq_right hh]
    unfold minusBoxEvenMoment minusMaskEvenMomentValue
    rw [upperMaskIntegral_const_mul]
    congr 1
    rw [upperMaskIntegral_finsetSum a b c H mask _ _ (by
      intro l₁
      apply continuous_finsetSum
      intro l₂ _
      apply continuous_finsetSum
      intro l₃ _
      split_ifs <;> fun_prop)]
    apply Finset.sum_congr rfl
    intro l₁ _
    rw [upperMaskIntegral_finsetSum a b c H mask _ _ (by
      intro l₂
      apply continuous_finsetSum
      intro l₃ _
      split_ifs <;> fun_prop)]
    apply Finset.sum_congr rfl
    intro l₂ _
    rw [upperMaskIntegral_finsetSum a b c H mask _ _ (by
      intro l₃
      split_ifs <;> fun_prop)]
    apply Finset.sum_congr rfl
    intro l₃ _
    by_cases hl : l₁.val+l₂.val+l₃.val = m
    · simp only [ite_eq_left hl]
      rw [upperMaskIntegral_div_const, simplexUpperMask_monomial_integral ha hb hc]
      rw [ite_eq_right hh]
    · simp only [ite_eq_right hl]
      simp

theorem minusMaskEvenMoment_slice_continuous (H : ℝ) (m : ℕ) :
    Continuous (fun r : Fin 2 → ℝ => minusBoxEvenMoment m (r 0) (r 1) (H-r 0-r 1)) := by
  unfold minusBoxEvenMoment
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro l₁ _
  apply continuous_finsetSum
  intro l₂ _
  apply continuous_finsetSum
  intro l₃ _
  split_ifs <;> fun_prop

theorem boundedSimplexSlice_minusBoxEvenMoment_masks {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (H : ℝ) (m : ℕ) :
    (∫ r, (boundedSimplexSlice a b c H).indicator
      (fun r => minusBoxEvenMoment m (r 0) (r 1) (H-r 0-r 1)) r) =
      ∑ mask : Fin 8, simplexMaskSign mask *
        (if H-simplexMaskShift a b c mask ≤ 0 then 0 else
          minusMaskEvenMomentValue m mask a b c (H-simplexMaskShift a b c mask)) := by
  rw [boundedSimplexSlice_integral_of_continuous a b c H _
    (minusMaskEvenMoment_slice_continuous H m)]
  simp_rw [simplexUpperMask_minusBoxEvenMoment_integral ha hb hc]

end Sechstmoment
