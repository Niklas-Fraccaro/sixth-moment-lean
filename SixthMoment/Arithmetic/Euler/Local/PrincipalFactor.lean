import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.NormNum.NatFactorial
import SixthMoment.Arithmetic.Euler.Local.Geometric.GeometricStep


open Complex Finset
open scoped BigOperators

namespace SixthMoment.Source
noncomputable section

def principalLocalFactor (x : ℂ) (h : ℕ) : ℂ :=
  (1-x)^4 * ((∑' k : ℕ, (((k+h)+3).choose 3 : ℂ) * x^(k+h)) -
    ((h+2).choose 3 : ℂ) * x^h/(1-x))

theorem principalLocalFactor_zero (x : ℂ) (hx : ‖x‖ < 1) :
    principalLocalFactor x 0 = 1 := by
  have hx1 : 1-x ≠ 0 := sub_ne_zero.mpr (by
    intro h
    rw [← h] at hx
    norm_num at hx)
  unfold principalLocalFactor
  simp only [Nat.add_zero, Nat.choose_eq_zero_of_lt (by norm_num : 2 < 3),
    Nat.cast_zero, zero_mul, zero_div, sub_zero]
  rw [tsum_choose_mul_geometric_of_norm_lt_one 3 hx]
  norm_num
  field_simp

theorem principalLocalFactor_succ (x : ℂ) (hx : ‖x‖ < 1) (h : ℕ) :
    principalLocalFactor x (h+1) = principalLocalFactor x h -
      (1-x)^3 * ((h+2).choose 2 : ℂ) * x^h := by
  have hs : Summable (fun k : ℕ => ((k+3).choose 3 : ℂ) * x^k) :=
    (hasSum_choose_mul_geometric_of_norm_lt_one 3 hx).summable
  have htail := hs.comp_injective (add_left_injective h)
  have ht := htail.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one] at ht
  have hsucc : ((h+3).choose 3 : ℂ) =
      ((h+2).choose 2 : ℂ) + ((h+2).choose 3 : ℂ) := by
    exact_mod_cast (Nat.choose_succ_succ (h+2) 2)
  have hx1 : 1-x ≠ 0 := sub_ne_zero.mpr (by
    intro he
    rw [← he] at hx
    norm_num at hx)
  unfold principalLocalFactor
  simp only [Function.comp_def] at ht
  simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
    Nat.add_zero, Nat.reduceAdd] at ht ⊢
  rw [hsucc] at ht ⊢
  rw [pow_succ]
  field_simp [hx1]
  simp only [← Nat.add_assoc] at ht
  linear_combination (1-x) * ht

theorem principalLocalFactor_eq_polynomial (x : ℂ) (hx : ‖x‖ < 1) (h : ℕ) :
    principalLocalFactor x h = x^h *
      (((h : ℂ)+2)*((h : ℂ)+1)/2 -
        (h : ℂ)*((h : ℂ)+2)*x + (h : ℂ)*((h : ℂ)+1)/2*x^2) := by
  induction h with
  | zero => simp [principalLocalFactor_zero x hx]
  | succ h ih =>
    rw [principalLocalFactor_succ x hx h, ih, Nat.cast_choose_two ℂ,
      Nat.cast_add, Nat.cast_ofNat]
    push_cast
    rw [pow_succ]
    ring

theorem principalLocalFactor_weighted_hasSum (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun h : ℕ => ((h : ℂ)+1)*principalLocalFactor x h)
      ((1+4*x+x^2)/(1-x)^2) := by
  have hx1 : 1-x ≠ 0 := sub_ne_zero.mpr (by
    intro he
    rw [← he] at hx
    norm_num at hx)
  have h0 := hasSum_geometric_of_norm_lt_one hx
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hx
  have h2 := hasSum_sq_mul_geometric_of_norm_lt_one hx
  have h3 : HasSum (fun h : ℕ => (h : ℂ)^3*x^h)
      (x*(1+4*x+x^2)/(1-x)^4) := by
    convert hasSum_pow_mul_geometric_of_norm_lt_one 3 hx using 1
    norm_num [Finset.sum_range_succ, Nat.stirlingSecond]
    field_simp [hx1]
    ring
  have hs := (((h3.mul_left ((1-x)^2/2)).add
    (h2.mul_left (2-3*x+x^2))).add
    (h1.mul_left ((5-4*x+x^2)/2))).add h0
  convert hs using 1
  · ext h
    rw [principalLocalFactor_eq_polynomial x hx h]
    ring
  · field_simp [hx1]
    ring

theorem principal_euler_factor (x : ℂ) (hx : ‖x‖ < 1) :
    (1-x)^6 * (∑' h : ℕ, ((h : ℂ)+1)*principalLocalFactor x h) =
      (1-x)^4*(1+4*x+x^2) := by
  rw [(principalLocalFactor_weighted_hasSum x hx).tsum_eq]
  have hx1 : 1-x ≠ 0 := sub_ne_zero.mpr (by
    intro he
    rw [← he] at hx
    norm_num at hx)
  field_simp [hx1]

theorem principal_euler_factor_prime (p : ℕ) (hp : p.Prime) :
    (1-(p : ℂ)⁻¹)^6 *
        (∑' h : ℕ, ((h : ℂ)+1)*principalLocalFactor ((p : ℂ)⁻¹) h) =
      (1-(p : ℂ)⁻¹)^4 * (1+4*(p : ℂ)⁻¹+((p : ℂ)⁻¹)^2) := by
  apply principal_euler_factor
  have hp' : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  simpa only [norm_inv, Complex.norm_natCast] using (inv_lt_one₀ (by positivity : (0 : ℝ) < p)).mpr hp'

end
end SixthMoment.Source
