import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Sechstmoment.Zeta.AFE.Two.Truncation

namespace Sechstmoment
open Complex Real Filter
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

def d02GaussianPowerConstant (A : ℝ) : ℝ :=
  1 + (Real.sqrt (2 * Real.pi) / Real.sqrt Real.pi) * Real.exp (2 * A ^ 2)

theorem d02GaussianPowerConstant_nonneg (A : ℝ) : 0 ≤ d02GaussianPowerConstant A := by
  unfold d02GaussianPowerConstant
  positivity

def d02GaussianPairAbsoluteTerm (a : ℕ × ℕ → ℂ) (Y : ℝ) (n : ℕ × ℕ) : ℝ :=
  ‖a n‖ * d02GaussianV0 (d02PositivePairProduct n / Y)

theorem d02GaussianPairAbsoluteTerm_power_bound (a : ℕ × ℕ → ℂ)
    {Y D A b : ℝ} (hY : 0 < Y) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (ha : ∀ n, ‖a n‖ ≤ D * (d02PositivePairProduct n) ^ (-b)) (n : ℕ × ℕ) :
    d02GaussianPairAbsoluteTerm a Y n ≤
      (D * d02GaussianPowerConstant A * Y ^ A) *
        (d02PositivePairProduct n) ^ (-(b + A)) := by
  have hp := d02PositivePairProduct_pos n
  have hw := d02GaussianV0_power_bound_all (div_pos hp hY) hA
  have he : (d02PositivePairProduct n) ^ (-b) *
      (d02PositivePairProduct n / Y) ^ (-A) =
        Y ^ A * (d02PositivePairProduct n) ^ (-(b + A)) := by
    rw [Real.div_rpow hp.le hY.le, Real.rpow_neg hY.le, div_inv_eq_mul]
    rw [show -(b + A) = -b + -A by ring, Real.rpow_add hp]
    ring
  unfold d02GaussianPairAbsoluteTerm
  calc
    _ ≤ (D * (d02PositivePairProduct n) ^ (-b)) *
        (d02GaussianPowerConstant A * (d02PositivePairProduct n / Y) ^ (-A)) :=
      mul_le_mul (ha n) hw (d02GaussianTail_nonneg _) (by positivity)
    _ = (D * d02GaussianPowerConstant A) *
        ((d02PositivePairProduct n) ^ (-b) * (d02PositivePairProduct n / Y) ^ (-A)) := by ring
    _ = _ := by rw [he]; ring

theorem d02GaussianPairAbsoluteTerm_summable (a : ℕ × ℕ → ℂ)
    {Y D A b : ℝ} (hY : 0 < Y) (hD : 0 ≤ D) (hA : 0 ≤ A) (hab : 1 < b + A)
    (ha : ∀ n, ‖a n‖ ≤ D * (d02PositivePairProduct n) ^ (-b)) :
    Summable (d02GaussianPairAbsoluteTerm a Y) := by
  apply ((d02_pair_power_summable hab).mul_left
    (D * d02GaussianPowerConstant A * Y ^ A)).of_nonneg_of_le
  · intro n
    exact mul_nonneg (norm_nonneg _) (d02GaussianTail_nonneg _)
  · exact d02GaussianPairAbsoluteTerm_power_bound a hY hD hA ha

theorem d02GaussianPairAbsoluteMass_bound (a : ℕ × ℕ → ℂ)
    {Y D A b : ℝ} (hY : 0 < Y) (hD : 0 ≤ D) (hA : 0 ≤ A) (hab : 1 < b + A)
    (ha : ∀ n, ‖a n‖ ≤ D * (d02PositivePairProduct n) ^ (-b)) :
    (∑' n, d02GaussianPairAbsoluteTerm a Y n) ≤
      (D * d02GaussianPowerConstant A * Y ^ A) *
        ∑' n : ℕ × ℕ, (d02PositivePairProduct n) ^ (-(b + A)) := by
  have hs := (d02_pair_power_summable hab).mul_left (D * d02GaussianPowerConstant A * Y ^ A)
  calc
    _ ≤ ∑' n : ℕ × ℕ, (D * d02GaussianPowerConstant A * Y ^ A) *
        (d02PositivePairProduct n) ^ (-(b + A)) :=
      (d02GaussianPairAbsoluteTerm_summable a hY hD hA hab ha).tsum_le_tsum
        (d02GaussianPairAbsoluteTerm_power_bound a hY hD hA ha) hs
    _ = _ := tsum_mul_left

def d02PairDirichletCoefficient (α : Fin 2 → ℂ) (n : ℕ × ℕ) : ℂ :=
  (n.1 + 1 : ℂ) ^ (-(1 / 2 : ℂ) - α 0) *
    (n.2 + 1 : ℂ) ^ (-(1 / 2 : ℂ) - α 1)

theorem d02PairDirichletCoefficient_norm_le {α : Fin 2 → ℂ} {b : ℝ}
    (hα : ∀ j, b - 1 / 2 ≤ (α j).re) (n : ℕ × ℕ) :
    ‖d02PairDirichletCoefficient α n‖ ≤ (d02PositivePairProduct n) ^ (-b) := by
  have hpoint (u : ℕ) (j : Fin 2) :
      ‖(u + 1 : ℂ) ^ (-(1 / 2 : ℂ) - α j)‖ ≤ (u + 1 : ℝ) ^ (-b) := by
    rw [show (u + 1 : ℂ) = ((u + 1 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (u + 1 : ℝ))]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) u] : (1 : ℝ) ≤ u + 1)
    have hh := hα j
    simp only [Complex.sub_re, Complex.neg_re]
    norm_num
    linarith
  unfold d02PairDirichletCoefficient d02PositivePairProduct
  rw [norm_mul, Real.mul_rpow (by positivity) (by positivity)]
  exact mul_le_mul (hpoint n.1 0) (hpoint n.2 1) (norm_nonneg _) (by positivity)

theorem d02RawShiftedGaussianPairAbsoluteMass_bound {Y T R ε : ℝ}
    (hY : 0 < Y) (hR : 0 ≤ R) (hε : 0 < ε)
    (hL : 0 < Real.log T) (hsmall : R / Real.log T ≤ ε)
    (σ : Fin 2 → ℂ) (hσ : ∀ j, ‖σ j‖ ≤ R) :
    (∑' n, d02GaussianPairAbsoluteTerm
      (d02PairDirichletCoefficient (fun j => σ j / (Real.log T : ℂ))) Y n) ≤
      (d02GaussianPowerConstant (1 / 2 + 2 * ε) * Y ^ (1 / 2 + 2 * ε)) *
        ∑' n : ℕ × ℕ, (d02PositivePairProduct n) ^ (-(1 + ε)) := by
  have hα : ∀ j, (1 / 2 - ε) - 1 / 2 ≤
      (σ j / (Real.log T : ℂ)).re := by
    intro j
    have hh := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hσ j))).1
    simp only [Complex.div_ofReal_re]
    have hlower := div_le_div_of_nonneg_right hh hL.le
    rw [neg_div] at hlower
    have hr := div_nonneg hR hL.le
    linarith
  have hb := d02GaussianPairAbsoluteMass_bound
    (d02PairDirichletCoefficient (fun j => σ j / (Real.log T : ℂ))) hY
    zero_le_one (by linarith : 0 ≤ (1 / 2 : ℝ) + 2 * ε)
    (by linarith : 1 < (1 / 2 - ε) + (1 / 2 + 2 * ε))
    (fun n => by simpa using d02PairDirichletCoefficient_norm_le hα n)
  have he : (1 / 2 - ε) + (1 / 2 + 2 * ε) = (1 : ℝ) + ε := by ring
  simpa only [one_mul, he] using hb

end
end Sechstmoment
