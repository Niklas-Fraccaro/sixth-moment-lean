import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Sechstmoment.Arithmetic.Divisors.LogFrequency

namespace Sechstmoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def d04ExponentialPairWeight (T : ℝ) (n : ℕ × ℕ) : ℝ :=
  Real.exp (-((n.1 + 1 : ℝ) * (n.2 + 1 : ℝ)) / T ^ (3 : ℕ))

def d04PairGeometricMajorant (T : ℝ) (n : ℕ × ℕ) : ℝ :=
  Real.exp (-(1 / (2 * T ^ (3 : ℕ)))) ^ n.1 *
    Real.exp (-(1 / (2 * T ^ (3 : ℕ)))) ^ n.2

theorem d04_exponential_pair_le_geometric {T : ℝ} (hT : 0 < T) (n : ℕ × ℕ) :
    d04ExponentialPairWeight T n ≤ d04PairGeometricMajorant T n := by
  unfold d04ExponentialPairWeight d04PairGeometricMajorant
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hx : (0 : ℝ) < T ^ (3 : ℕ) := pow_pos hT _
  have h0 : (0 : ℝ) ≤ n.1 := Nat.cast_nonneg _
  have h1 : (0 : ℝ) ≤ n.2 := Nat.cast_nonneg _
  have hh : (n.1 : ℝ) + n.2 ≤ 2 * ((n.1 + 1 : ℝ) * (n.2 + 1 : ℝ)) := by
    nlinarith [mul_nonneg h0 h1]
  have hh' := div_le_div_of_nonneg_right hh hx.le
  field_simp at hh' ⊢
  nlinarith

theorem d04_pair_geometric_summable {T : ℝ} (hT : 0 < T) :
    Summable (d04PairGeometricMajorant T) := by
  have hr : Real.exp (-(1 / (2 * T ^ (3 : ℕ)))) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (by positivity)
  have hs := summable_geometric_of_lt_one
    (Real.exp_pos (-(1 / (2 * T ^ (3 : ℕ))))).le hr
  exact hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)

theorem d04_pair_geometric_tsum {T : ℝ} (hT : 0 < T) :
    (∑' n : ℕ × ℕ, d04PairGeometricMajorant T n) =
      (1 - Real.exp (-(1 / (2 * T ^ (3 : ℕ)))))⁻¹ ^ (2 : ℕ) := by
  have hr : Real.exp (-(1 / (2 * T ^ (3 : ℕ)))) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (by positivity)
  have hs := summable_geometric_of_lt_one
    (Real.exp_pos (-(1 / (2 * T ^ (3 : ℕ))))).le hr
  unfold d04PairGeometricMajorant
  rw [← hs.tsum_mul_tsum hs (d04_pair_geometric_summable hT),
    tsum_geometric_of_lt_one (Real.exp_pos _).le hr]
  ring

theorem d04_pair_geometric_tsum_le {T : ℝ} (hT : 1 ≤ T) :
    (∑' n : ℕ × ℕ, d04PairGeometricMajorant T n) ≤ 9 * T ^ (6 : ℕ) := by
  have ht : 0 < T := zero_lt_one.trans_le hT
  have hx : 0 < 1 / (2 * T ^ (3 : ℕ)) := by positivity
  have hr : Real.exp (-(1 / (2 * T ^ (3 : ℕ)))) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  have hexp := Real.add_one_le_exp (1 / (2 * T ^ (3 : ℕ)))
  have he : Real.exp (-(1 / (2 * T ^ (3 : ℕ)))) ≤
      1 / (1 + 1 / (2 * T ^ (3 : ℕ))) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hden : 1 / (2 * T ^ (3 : ℕ) + 1) ≤
      1 - Real.exp (-(1 / (2 * T ^ (3 : ℕ)))) := by
    have hcalc : 1 - 1 / (1 + 1 / (2 * T ^ (3 : ℕ))) =
        1 / (2 * T ^ (3 : ℕ) + 1) := by
      field_simp
      ring
    linarith
  have hinv : (1 - Real.exp (-(1 / (2 * T ^ (3 : ℕ)))))⁻¹ ≤
      2 * T ^ (3 : ℕ) + 1 := by
    have hh := one_div_le_one_div_of_le (by positivity) hden
    simpa only [one_div_one_div, inv_eq_one_div] using hh
  have hp : 1 ≤ T ^ (3 : ℕ) := one_le_pow₀ hT
  have hbig : (1 - Real.exp (-(1 / (2 * T ^ (3 : ℕ)))))⁻¹ ≤
      3 * T ^ (3 : ℕ) := by linarith
  rw [d04_pair_geometric_tsum ht]
  have hn : 0 ≤ (1 - Real.exp (-(1 / (2 * T ^ (3 : ℕ)))))⁻¹ := by positivity
  calc
    _ ≤ (3 * T ^ (3 : ℕ)) ^ (2 : ℕ) := pow_le_pow_left₀ hn hbig _
    _ = _ := by ring

theorem d04_exponential_pair_summable {T : ℝ} (hT : 0 < T) :
    Summable (d04ExponentialPairWeight T) :=
  Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le)
    (d04_exponential_pair_le_geometric hT) (d04_pair_geometric_summable hT)

theorem d04_exponential_pair_tsum_le {T : ℝ} (hT : 1 ≤ T) :
    (∑' n : ℕ × ℕ, d04ExponentialPairWeight T n) ≤ 9 * T ^ (6 : ℕ) := by
  have ht : 0 < T := zero_lt_one.trans_le hT
  exact ((d04_exponential_pair_summable ht).tsum_le_tsum
    (d04_exponential_pair_le_geometric ht) (d04_pair_geometric_summable ht)).trans
    (d04_pair_geometric_tsum_le hT)

theorem d04_exponential_coefficient_mass {T C : ℝ} (hT : 1 ≤ T) (hC : 0 ≤ C)
    (c : ℕ × ℕ → ℂ)
    (hc : ∀ n, ‖c n‖ ≤ C * d04ExponentialPairWeight T n) :
    Summable (fun n => ‖c n‖) ∧ (∑' n, ‖c n‖) ≤ 9 * C * T ^ (6 : ℕ) := by
  have ht : 0 < T := zero_lt_one.trans_le hT
  have hg := (d04_exponential_pair_summable ht).mul_left C
  have hs := Summable.of_nonneg_of_le (fun n => norm_nonneg (c n)) hc hg
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' n, C * d04ExponentialPairWeight T n := hs.tsum_le_tsum hc hg
    _ = C * ∑' n, d04ExponentialPairWeight T n := tsum_mul_left
    _ ≤ C * (9 * T ^ (6 : ℕ)) :=
      mul_le_mul_of_nonneg_left (d04_exponential_pair_tsum_le hT) hC
    _ = _ := by ring

end
end Sechstmoment
