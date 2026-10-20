import Sechstmoment.Analysis.Complex.PositivePowers
import Sechstmoment.Analysis.Fourier.ProfileProduct

namespace Sechstmoment
open Complex Real Set MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 700000

theorem a03TimePowerProfile_fourier_decay {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {R : ℝ} (hR : 0≤R) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ q : ℂ,q.re≤R → ∀ ξ : ℝ,
      (1+|ξ|)^N*‖profileLaplaceTransform
        (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^q)) ((ξ:ℂ)*I)‖≤C*(1+‖q‖)^N := by
  obtain ⟨P,hP,hfreq⟩ := a03_profile_product_uniform_frequency_bound hΦ hSupp
  let B : ℕ→ℝ := fun j => ((j:ℝ)+1)^j*2^R
  have hB (j : ℕ) : 0≤B j := by dsimp [B]; positivity
  let K : ℕ→ℝ := a03ProfileProductDerivativeBudget P B
  have hK (j : ℕ) : 0≤K j := by
    unfold K a03ProfileProductDerivativeBudget
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg (j.choose i)) (hP i)) (hB (j-i))
  have hdec (j : ℕ) (q : ℂ) (hq : q.re≤R) (ξ : ℝ) :
      |ξ|^j*‖profileLaplaceTransform (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^q)) ((ξ:ℂ)*I)‖≤
        K j*(1+‖q‖)^j := by
    let Bq : ℕ→ℝ := fun k => B k*(1+‖q‖)^k
    have hBq (k : ℕ) : 0≤Bq k := mul_nonneg (hB k) (by positivity)
    have hA (t : ℝ) (ht : t∈Icc (1:ℝ) 2) :
        ContDiffAt ℝ ∞ (fun t : ℝ => (t:ℂ)^q) t :=
      positive_cpow_contDiffAt q (zero_lt_one.trans_le ht.1)
    have hd (k : ℕ) (t : ℝ) (ht : t∈Icc (1:ℝ) 2) :
        ‖iteratedDeriv k (fun t : ℝ => (t:ℂ)^q) t‖≤Bq k*1 := by
      have htp : 0<t := zero_lt_one.trans_le ht.1
      have hp : t^(q.re-(k:ℝ))≤2^R := by
        exact (Real.rpow_le_rpow_of_exponent_le ht.1 (by linarith only [hq,(Nat.cast_nonneg k : (0:ℝ)≤k)])).trans
          (Real.rpow_le_rpow htp.le ht.2 hR)
      rw [positive_cpow_iteratedDeriv k q htp,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos htp,
        Complex.sub_re,Complex.natCast_re]
      calc
        _≤(((k:ℝ)+1)^k*(1+‖q‖)^k)*2^R := mul_le_mul
          (mellinFallingCoefficient_norm_le k q) hp (Real.rpow_nonneg htp.le _) (by positivity)
        _=Bq k*1 := by dsimp only [Bq,B]; ring
    have hh := hfreq (fun t : ℝ => (t:ℂ)^q) hA Bq hBq 1 zero_le_one hd j ξ
    apply hh.trans
    rw [mul_one]
    dsimp only [K]
    unfold a03ProfileProductDerivativeBudget
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    dsimp only [Bq]
    have hp : (1+‖q‖)^(j-i)≤(1+‖q‖)^j := pow_le_pow_right₀ (by linarith only [norm_nonneg q]) (Nat.sub_le _ _)
    convert mul_le_mul_of_nonneg_left hp
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg (j.choose i)) (hP i)) (hB (j-i))) using 1
    ring
  have hKN := hK N
  have hK0 := hK 0
  refine ⟨2^N*(K N+K 0),by positivity,?_⟩
  intro q hq ξ
  have hd := hdec N q hq ξ
  have hz := hdec 0 q hq ξ
  simp only [pow_zero,one_mul,mul_one] at hz
  have hD : 1≤(1+‖q‖)^N := one_le_pow₀ (by linarith only [norm_nonneg q])
  have hp : (1+|ξ|)^N≤2^N*(1+|ξ|^N) := by
    by_cases hξ : |ξ|≤1
    · calc
        _≤(2:ℝ)^N := pow_le_pow_left₀ (by positivity) (by linarith only [hξ]) N
        _≤_ := by nlinarith only [pow_nonneg (abs_nonneg ξ) N,pow_nonneg (by norm_num : (0:ℝ)≤2) N]
    · have hξ' : 1≤|ξ| := le_of_lt (lt_of_not_ge hξ)
      calc
        _≤(2*|ξ|)^N := pow_le_pow_left₀ (by positivity) (by linarith only [hξ']) N
        _=2^N*|ξ|^N := mul_pow _ _ _
        _≤_ := by nlinarith only [pow_nonneg (abs_nonneg ξ) N,pow_nonneg (by norm_num : (0:ℝ)≤2) N]
  calc
    _≤2^N*(1+|ξ|^N)*‖profileLaplaceTransform
      (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^q)) ((ξ:ℂ)*I)‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _=2^N*(‖profileLaplaceTransform (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^q)) ((ξ:ℂ)*I)‖+
      |ξ|^N*‖profileLaplaceTransform (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^q)) ((ξ:ℂ)*I)‖) := by ring
    _≤2^N*(K 0*(1+‖q‖)^N+K N*(1+‖q‖)^N) :=
      mul_le_mul_of_nonneg_left (add_le_add
        (hz.trans (le_mul_of_one_le_right hK0 hD)) hd) (by positivity)
    _=_ := by ring

end
end Sechstmoment
