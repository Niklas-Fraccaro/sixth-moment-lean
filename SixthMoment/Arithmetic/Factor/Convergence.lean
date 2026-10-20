import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import SixthMoment.Arithmetic.Factor.Definitions

namespace SixthMoment

theorem eulerFactor_sub_one_bound (p : {n : ℕ // Nat.Prime n}) :
    ‖eulerFactor (p.val : ℝ) - 1‖ ≤ 35 / (p.val : ℝ)^2 := by
  let x : ℝ := 1 / (p.val : ℝ)
  have hp : 1 < (p.val : ℝ) := by exact_mod_cast p.property.one_lt
  have hx₀ : 0 ≤ x := by dsimp [x]; positivity
  have hx₁ : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one (by linarith)).mpr hp.le
  have hx₂ : x^2 ≤ 1 := pow_le_one₀ hx₀ hx₁
  have hx₄ : x^4 ≤ 1 := pow_le_one₀ hx₀ hx₁
  have ha : |(-9 : ℝ)+16*x-9*x^2+x^4| ≤ 35 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg x, pow_nonneg hx₀ 4]
  have he : eulerFactor (p.val : ℝ)-1 = x^2*(-9+16*x-9*x^2+x^4) := by
    dsimp [eulerFactor, x]
    ring
  rw [he, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg x)]
  calc
    x^2*|(-9 : ℝ)+16*x-9*x^2+x^4| ≤ x^2*35 :=
      mul_le_mul_of_nonneg_left ha (sq_nonneg x)
    _ = 35/(p.val : ℝ)^2 := by dsimp [x]; ring

theorem eulerFactor_sub_one_summable :
    Summable (fun p : {n : ℕ // Nat.Prime n} => eulerFactor (p.val : ℝ)-1) := by
  have hs : Summable (fun n : ℕ => 1/(n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have ht : Summable (fun p : {n : ℕ // Nat.Prime n} => 35/(p.val : ℝ)^2) := by
    apply ((hs.subtype Nat.Prime).mul_left 35).congr
    intro p
    change 35*(1/(p.val : ℝ)^2) = 35/(p.val : ℝ)^2
    ring
  exact ht.of_norm_bounded eulerFactor_sub_one_bound

theorem eulerFactor_log_summable :
    Summable (fun p : {n : ℕ // Nat.Prime n} => Real.log (eulerFactor (p.val : ℝ))) := by
  simpa only [add_sub_cancel] using
    Real.summable_log_one_add_of_summable eulerFactor_sub_one_summable

theorem arithmeticFactor_wellDefined : ArithmeticFactorWellDefined := by
  constructor
  · exact Real.multipliable_of_summable_log eulerFactor_prime_pos eulerFactor_log_summable
  · unfold arithmeticFactor
    rw [← Real.rexp_tsum_eq_tprod eulerFactor_prime_pos eulerFactor_log_summable]
    exact Real.exp_pos _

end SixthMoment
