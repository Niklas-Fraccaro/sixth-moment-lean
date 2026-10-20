import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import Sechstmoment.Analysis.Asymptotics.PowerLog
import Sechstmoment.Analysis.Complex.FiniteSum


namespace Sechstmoment

open Filter Asymptotics
open scoped Topology BigOperators

noncomputable def rectangularSlack (a b : ℝ) : ℝ := (2 - 3 * a - 5 * b) / 32

noncomputable def rectangularFirstExponent (a b δ : ℝ) : ℝ := 1 / 2 + a + b + δ

noncomputable def rectangularSecondExponent (a b δ : ℝ) : ℝ :=
  3 / 4 + 3 * a / 8 + 5 * b / 8 + δ

theorem rectangular_slack_bounds {a b : ℝ} (hab : a ≤ b) (h : 3 * a + 5 * b < 2) :
    0 < rectangularSlack a b ∧
      rectangularFirstExponent a b (rectangularSlack a b) + rectangularSlack a b < 1 ∧
      rectangularSecondExponent a b (rectangularSlack a b) + rectangularSlack a b < 1 := by
  dsimp [rectangularSlack, rectangularFirstExponent, rectangularSecondExponent]
  constructor
  · linarith
  constructor <;> linarith

theorem rectangular_exponents_exist {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h : 3 * a + 5 * b < 2) :
    ∃ δ : ℝ, 0 < δ ∧
      0 < rectangularFirstExponent a b δ ∧ rectangularFirstExponent a b δ < 1 ∧
      0 < rectangularSecondExponent a b δ ∧ rectangularSecondExponent a b δ < 1 := by
  obtain ⟨hd, h₁, h₂⟩ := rectangular_slack_bounds hab h
  refine ⟨rectangularSlack a b, hd, ?_, ?_, ?_, ?_⟩
  · dsimp [rectangularFirstExponent]
    linarith
  · linarith
  · dsimp [rectangularSecondExponent]
    linarith
  · linarith

theorem rectangular_power_sum_isLittleO {a b : ℝ} (hab : a ≤ b)
    (h : 3 * a + 5 * b < 2) :
    (fun T : ℝ => T ^ rectangularFirstExponent a b (rectangularSlack a b) +
      T ^ rectangularSecondExponent a b (rectangularSlack a b)) =o[atTop]
      (fun T : ℝ => T) := by
  obtain ⟨hd, h₁, h₂⟩ := rectangular_slack_bounds hab h
  exact (rpow_isLittleO_id_of_lt_one (by linarith :
    rectangularFirstExponent a b (rectangularSlack a b) < 1)).add
    (rpow_isLittleO_id_of_lt_one (by linarith :
      rectangularSecondExponent a b (rectangularSlack a b) < 1))

theorem polylog_weighted_power_sum_isLittleO {a b : ℝ} (hab : a ≤ b)
    (h : 3 * a + 5 * b < 2) (n : ℕ) :
    (fun T : ℝ => (Real.log T) ^ n *
      (T ^ rectangularFirstExponent a b (rectangularSlack a b) +
        T ^ rectangularSecondExponent a b (rectangularSlack a b))) =o[atTop]
      (fun T : ℝ => T) := by
  obtain ⟨hd, h₁, h₂⟩ := rectangular_slack_bounds hab h
  simpa only [mul_add] using
    (polylog_mul_rpow_isLittleO_id n (by linarith :
      rectangularFirstExponent a b (rectangularSlack a b) < 1)).add
    (polylog_mul_rpow_isLittleO_id n (by linarith :
      rectangularSecondExponent a b (rectangularSlack a b) < 1))

theorem rectangular_finset_sum_isLittleO {ι : Type*} {a b C D : ℝ}
    (hab : a ≤ b) (h : 3 * a + 5 * b < 2) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (n : ℕ) (s : ℝ → Finset ι) (F : ι → ℝ → ℂ)
    (hcard : ∀ᶠ T in atTop, ((s T).card : ℝ) ≤ C * (Real.log T) ^ n)
    (hblock : ∀ᶠ T in atTop, ∀ i ∈ s T,
      ‖F i T‖ ≤ D *
        (T ^ rectangularFirstExponent a b (rectangularSlack a b) +
          T ^ rectangularSecondExponent a b (rectangularSlack a b))) :
    (fun T => ∑ i ∈ s T, F i T) =o[atTop] (fun T : ℝ => T) := by
  have hbound : ∀ᶠ T in atTop,
      ‖∑ i ∈ s T, F i T‖ ≤ (C * D) * ((Real.log T) ^ n *
        (T ^ rectangularFirstExponent a b (rectangularSlack a b) +
          T ^ rectangularSecondExponent a b (rectangularSlack a b))) := by
    filter_upwards [hcard, hblock, eventually_ge_atTop (1 : ℝ)] with T hc hb hT
    have hpow : 0 ≤ T ^ rectangularFirstExponent a b (rectangularSlack a b) +
        T ^ rectangularSecondExponent a b (rectangularSlack a b) := by
      exact add_nonneg (Real.rpow_nonneg (by linarith) _)
        (Real.rpow_nonneg (by linarith) _)
    calc
      ‖∑ i ∈ s T, F i T‖ ≤ ((s T).card : ℝ) * (D *
        (T ^ rectangularFirstExponent a b (rectangularSlack a b) +
          T ^ rectangularSecondExponent a b (rectangularSlack a b))) :=
        complex_finset_sum_norm_le_card_mul (s T) (fun i => F i T) hb
      _ ≤ (C * (Real.log T) ^ n) * (D *
        (T ^ rectangularFirstExponent a b (rectangularSlack a b) +
          T ^ rectangularSecondExponent a b (rectangularSlack a b))) :=
        mul_le_mul hc (le_refl _) (mul_nonneg hD hpow)
          (mul_nonneg hC (pow_nonneg (Real.log_nonneg hT) n))
      _ = _ := by ring
  have hresult := (polylog_weighted_power_sum_isLittleO hab h n).const_mul_left (C * D)
  exact hbound.isBigO.trans_isLittleO hresult

end Sechstmoment
