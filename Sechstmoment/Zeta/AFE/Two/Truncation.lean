import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Sechstmoment.Analysis.Gaussian.Weight

namespace Sechstmoment
open Real Complex Filter
open scoped BigOperators
noncomputable section

def d02PositivePairProduct (n : ℕ × ℕ) : ℝ := (n.1+1:ℝ)*(n.2+1:ℝ)

theorem d02PositivePairProduct_pos (n : ℕ × ℕ) : 0 < d02PositivePairProduct n := by
  unfold d02PositivePairProduct
  positivity

theorem d02_pair_power_summable {b : ℝ} (hb : 1 < b) :
    Summable (fun n : ℕ × ℕ => (d02PositivePairProduct n)^(-b)) := by
  have hs : Summable (fun n : ℕ => (n+1:ℝ)^(-b)) := by
    convert ((Real.summable_one_div_nat_add_rpow 1 b).mpr hb) using 1
    funext n
    rw [abs_of_pos (by positivity : (0:ℝ)<n+1),
      Real.rpow_neg (by positivity : (0:ℝ)≤n+1)]
    simp only [one_div]
  have h := hs.mul_of_nonneg hs (fun n => by positivity) (fun n => by positivity)
  convert h using 1
  funext n
  exact Real.mul_rpow (by positivity) (by positivity)

def d02PairMass : ℝ := ∑' n : ℕ × ℕ, (d02PositivePairProduct n)^(-2:ℝ)

theorem d02PairMass_nonneg : 0 ≤ d02PairMass :=
  tsum_nonneg (fun _ => Real.rpow_nonneg (le_of_lt (d02PositivePairProduct_pos _)) _)

def d02GaussianLongTail (a : ℕ × ℕ → ℂ) (X Y : ℝ) (n : ℕ × ℕ) : ℝ :=
  if X < d02PositivePairProduct n then
    ‖a n‖ * d02GaussianV0 (d02PositivePairProduct n/Y)
  else 0

theorem d02GaussianLongTail_term_bound
    (a : ℕ × ℕ → ℂ) {X Y A b : ℝ} (hY : 0 < Y) (hX : Y ≤ X)
    (hA : 2 ≤ A+b) (ha : ∀ n, ‖a n‖ ≤ (d02PositivePairProduct n)^(-b))
    (n : ℕ × ℕ) :
    d02GaussianLongTail a X Y n ≤
      ((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2)*
        Y^A*X^(2-b-A)) * (d02PositivePairProduct n)^(-2:ℝ) := by
  have hXp : 0 < X := hY.trans_le hX
  have hp := d02PositivePairProduct_pos n
  have hC : 0 ≤ (Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2) := by
    positivity
  by_cases hn : X < d02PositivePairProduct n
  · rw [d02GaussianLongTail, ite_eq_left hn]
    have hr : 1 ≤ d02PositivePairProduct n/Y :=
      (le_div_iff₀ hY).mpr (by linarith)
    have hw := d02GaussianV0_power_bound hr A
    have he : (d02PositivePairProduct n)^(-b) *
        (d02PositivePairProduct n/Y)^(-A) =
        Y^A * (d02PositivePairProduct n)^(2-b-A) *
          (d02PositivePairProduct n)^(-2:ℝ) := by
      rw [Real.div_rpow hp.le hY.le, Real.rpow_neg hY.le, div_inv_eq_mul]
      have hpows : (d02PositivePairProduct n)^(2-b-A) *
          (d02PositivePairProduct n)^(-2:ℝ) =
            (d02PositivePairProduct n)^(-b) * (d02PositivePairProduct n)^(-A) := by
        rw [← Real.rpow_add hp, ← Real.rpow_add hp]
        congr 1
        ring
      rw [mul_assoc (Y^A), hpows]
      ring
    have hpow : (d02PositivePairProduct n)^(2-b-A) ≤ X^(2-b-A) :=
      Real.rpow_le_rpow_of_nonpos hXp hn.le (by linarith)
    calc
      _ ≤ (d02PositivePairProduct n)^(-b) *
          ((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2)*
            (d02PositivePairProduct n/Y)^(-A)) :=
        mul_le_mul (ha n) hw (d02GaussianTail_nonneg _) (by positivity)
      _ = ((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2)) *
          (Y^A * (d02PositivePairProduct n)^(2-b-A) *
            (d02PositivePairProduct n)^(-2:ℝ)) := by rw [← he]; ring
      _ = (((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2))*
          Y^A*(d02PositivePairProduct n)^(2-b-A))*
          (d02PositivePairProduct n)^(-2:ℝ) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
  · rw [d02GaussianLongTail, ite_eq_right hn]
    positivity

theorem d02GaussianLongTail_summable
    (a : ℕ × ℕ → ℂ) {X Y A b : ℝ} (hY : 0 < Y) (hX : Y ≤ X)
    (hA : 2 ≤ A+b) (ha : ∀ n, ‖a n‖ ≤ (d02PositivePairProduct n)^(-b)) :
    Summable (d02GaussianLongTail a X Y) := by
  apply ((d02_pair_power_summable (by norm_num : (1:ℝ) < 2)).mul_left
    ((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2)*
      Y^A*X^(2-b-A))).of_nonneg_of_le
  · intro n
    unfold d02GaussianLongTail
    split_ifs
    · exact mul_nonneg (norm_nonneg _) (d02GaussianTail_nonneg _)
    · exact le_rfl
  · exact d02GaussianLongTail_term_bound a hY hX hA ha

theorem d02GaussianLongTail_tsum_bound
    (a : ℕ × ℕ → ℂ) {X Y A b : ℝ} (hY : 0 < Y) (hX : Y ≤ X)
    (hA : 2 ≤ A+b) (ha : ∀ n, ‖a n‖ ≤ (d02PositivePairProduct n)^(-b)) :
    (∑' n, d02GaussianLongTail a X Y n) ≤
      ((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2)*
        Y^A*X^(2-b-A)) * d02PairMass := by
  have hs := (d02_pair_power_summable (by norm_num : (1:ℝ) < 2)).mul_left
    ((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2)*
      Y^A*X^(2-b-A))
  calc
    _ ≤ ∑' n, ((Real.sqrt (2*Real.pi)/Real.sqrt Real.pi)*Real.exp (2*A^2)*
        Y^A*X^(2-b-A)) * (d02PositivePairProduct n)^(-2:ℝ) :=
      (d02GaussianLongTail_summable a hY hX hA ha).tsum_le_tsum
        (d02GaussianLongTail_term_bound a hY hX hA ha) hs
    _ = _ := by rw [tsum_mul_left]; rfl

end
end Sechstmoment
