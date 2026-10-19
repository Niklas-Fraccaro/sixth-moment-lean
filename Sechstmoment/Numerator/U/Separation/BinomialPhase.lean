import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Sechstmoment.Analysis.Complex.PositivePowers
import Sechstmoment.Arithmetic.QuadraticDivisor.Definitions

/-! Exact convergent binomial separation of the signed logarithmic phase.
The quantitative tail is a proved tail of this actual series. -/
namespace Sechstmoment
open Complex Real Set Filter Polynomial
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def phaseBinomialCoefficient (s : ℂ) (k : ℕ) : ℂ :=
  mellinFallingCoefficient k s/(k.factorial : ℂ)

def phaseBinomialMajorant (a : ℝ) (k : ℕ) : ℝ :=
  (∏ i∈Finset.range k, (a+(i:ℝ)))/(k.factorial : ℝ)

private theorem falling_eq_desc (s : ℂ) (k : ℕ) :
    mellinFallingCoefficient k s=(descPochhammer ℤ k).smeval s := by
  induction k with
  | zero => simp [mellinFallingCoefficient]
  | succ k ih =>
    rw [mellinFallingCoefficient_succ,descPochhammer_succ_right,Polynomial.smeval_mul,← ih]
    congr 1
    simp
    rw [← Polynomial.C_eq_natCast,Polynomial.smeval_C]
    simp

theorem phaseBinomialCoefficient_eq_choose (s : ℂ) (k : ℕ) :
    phaseBinomialCoefficient s k=Ring.choose s k := by
  unfold phaseBinomialCoefficient
  rw [falling_eq_desc,Ring.descPochhammer_eq_factorial_smul_choose,nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast Nat.factorial_ne_zero k)

theorem phaseBinomial_hasSum (s x : ℂ) (hx : ‖x‖<1) :
    HasSum (fun k : ℕ => phaseBinomialCoefficient s k*x^k) ((1+x)^s) := by
  have hx' : x∈Metric.eball (0:ℂ) (1:ENNReal) := by
    rw [← ENNReal.ofReal_one,Metric.eball_ofReal,Metric.mem_ball,dist_zero_right]
    exact hx
  have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := s)).hasSum hx'
  simpa [binomialSeries,FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul,phaseBinomialCoefficient_eq_choose,mul_comm] using h

theorem phaseBinomialMajorant_nonneg {a : ℝ} (ha : 0≤a) (k : ℕ) :
    0≤phaseBinomialMajorant a k := by
  unfold phaseBinomialMajorant
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.prod_nonneg (fun i _ => add_nonneg ha (Nat.cast_nonneg i))

private theorem negative_real_coefficient (a : ℝ) (k : ℕ) :
    phaseBinomialCoefficient (-(a:ℂ)) k=(-1:ℂ)^k*(phaseBinomialMajorant a k:ℂ) := by
  unfold phaseBinomialCoefficient mellinFallingCoefficient phaseBinomialMajorant
  push_cast
  have hp : (∏ i∈Finset.range k, (-(a:ℂ)-(i:ℂ)))=
      (-1:ℂ)^k*∏ i∈Finset.range k, ((a:ℂ)+(i:ℂ)) := by
    simp_rw [show ∀ i : ℕ, -(a:ℂ)-(i:ℂ)=(-1:ℂ)*((a:ℂ)+(i:ℂ)) by intro i; ring]
    rw [Finset.prod_mul_distrib]
    simp
  rw [hp]
  ring

theorem phaseBinomialCoefficient_imaginary_norm_le (t : ℝ) (k : ℕ) :
    ‖phaseBinomialCoefficient (-(t:ℂ)*I) k‖≤phaseBinomialMajorant |t| k := by
  unfold phaseBinomialCoefficient phaseBinomialMajorant
  rw [norm_div,Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  unfold mellinFallingCoefficient
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro i _
  have hn := norm_sub_le (-(t:ℂ)*I) (i:ℂ)
  simpa only [norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_I,mul_one,Complex.norm_natCast] using hn

private theorem majorant_term_identity (a r : ℝ) (k : ℕ) :
    phaseBinomialCoefficient (-(a:ℂ)) k*(-(r:ℂ))^k=
      (phaseBinomialMajorant a k*r^k:ℝ) := by
  rw [negative_real_coefficient,neg_pow]
  push_cast
  have hsign : (-1:ℂ)^k*(-1:ℂ)^k=1 := by rw [← mul_pow]; simp
  calc
    _ = ((-1:ℂ)^k*(-1:ℂ)^k)*((phaseBinomialMajorant a k:ℂ)*(r:ℂ)^k) := by ring
    _ = _ := by rw [hsign,one_mul]

theorem phaseBinomialMajorant_hasSum {a r : ℝ} (_ha : 0≤a) (hr : 0≤r) (hr1 : r<1) :
    HasSum (fun k : ℕ => phaseBinomialMajorant a k*r^k) ((1-r)^(-a)) := by
  have hs := phaseBinomial_hasSum (-(a:ℂ)) (-(r:ℂ))
    (by simpa only [norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr] using hr1)
  simp_rw [majorant_term_identity] at hs
  have he : ((1-(r:ℂ))^(-(a:ℂ))).re=(1-r)^(-a) := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,← Complex.ofReal_neg,
      ← Complex.ofReal_cpow (by linarith : 0≤1-r)]
    rfl
  simpa only [Complex.reCLM_apply,Complex.ofReal_re,show (1:ℂ)+-(r:ℂ)=1-(r:ℂ) by ring,he]
    using Complex.reCLM.hasSum hs

theorem phaseBinomial_remainder_bound {r : ℝ} (hr : 0≤r) (hr2 : 2*r<1)
    (t : ℝ) (x : ℂ) (hx : ‖x‖≤r) (N : ℕ) :
    ‖(1+x)^(-(t:ℂ)*I)-∑ k∈Finset.range N,
      phaseBinomialCoefficient (-(t:ℂ)*I) k*x^k‖≤
        (1/(2:ℝ)^N)*(1-2*r)^(-|t|) := by
  let f : ℕ → ℂ := fun k => phaseBinomialCoefficient (-(t:ℂ)*I) k*x^k
  let B : ℕ → ℝ := fun k => phaseBinomialMajorant |t| k*(2*r)^k
  have hs := phaseBinomial_hasSum (-(t:ℂ)*I) x (hx.trans_lt (by linarith))
  have hB := phaseBinomialMajorant_hasSum (abs_nonneg t) (by linarith : 0≤2*r) hr2
  change HasSum f ((1+x)^(-(t:ℂ)*I)) at hs
  change HasSum B ((1-2*r)^(-|t|)) at hB
  have hBn (k : ℕ) : 0≤B k :=
    mul_nonneg (phaseBinomialMajorant_nonneg (abs_nonneg t) k) (pow_nonneg (by linarith) k)
  have heq : (1+x)^(-(t:ℂ)*I)-∑ k∈Finset.range N, f k=∑' k : ℕ, f (k+N) := by
    have hsplit : (∑ k∈Finset.range N, f k)+(∑' k : ℕ, f (k+N))=∑' k : ℕ, f k :=
      (hs.summable.comp_injective (add_left_injective N)).sum_add_tsum_nat_add'
    rw [← hs.tsum_eq,← hsplit]
    exact add_sub_cancel_left _ _
  have hp (k : ℕ) : ‖f (k+N)‖≤(1/(2:ℝ)^N)*B (k+N) := by
    dsimp [f,B]
    rw [norm_mul,norm_pow]
    calc
      _ ≤ phaseBinomialMajorant |t| (k+N)*r^(k+N) :=
        mul_le_mul (phaseBinomialCoefficient_imaginary_norm_le t (k+N))
          (pow_le_pow_left₀ (norm_nonneg x) hx (k+N)) (by positivity)
          (phaseBinomialMajorant_nonneg (abs_nonneg t) (k+N))
      _ ≤ (1/(2:ℝ)^N)*(phaseBinomialMajorant |t| (k+N)*(2*r)^(k+N)) := by
        have h2 : (1:ℝ)≤2^k := one_le_pow₀ (by norm_num)
        have hn := mul_le_mul_of_nonneg_right h2 (pow_nonneg hr (k+N))
        have he : (1/(2:ℝ)^N)*(2*r)^(k+N)=2^k*r^(k+N) := by
          rw [mul_pow,pow_add]
          field_simp
        calc
          _ ≤ phaseBinomialMajorant |t| (k+N)*(2^k*r^(k+N)) :=
            mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hn)
              (phaseBinomialMajorant_nonneg (abs_nonneg t) (k+N))
          _ = _ := by rw [← he]; ring
  have htail : (∑' k : ℕ, B (k+N))≤(1-2*r)^(-|t|) := by
    have hh : (∑ k∈Finset.range N, B k)+(∑' k : ℕ, B (k+N))=∑' k : ℕ, B k :=
      (hB.summable.comp_injective (add_left_injective N)).sum_add_tsum_nat_add'
    have hsum : 0≤∑ k∈Finset.range N, B k := Finset.sum_nonneg (fun k _ => hBn k)
    have he : (∑' k : ℕ, B k)=(1-2*r)^(-|t|) := hB.tsum_eq
    linarith
  rw [heq]
  calc
    _ ≤ ∑' k : ℕ, ‖f (k+N)‖ :=
      norm_tsum_le_tsum_norm (hs.summable.norm.comp_injective (add_left_injective N))
    _ ≤ ∑' k : ℕ, (1/(2:ℝ)^N)*B (k+N) :=
      (hs.summable.norm.comp_injective (add_left_injective N)).tsum_le_tsum hp
        ((hB.summable.comp_injective (add_left_injective N)).mul_left _)
    _ = (1/(2:ℝ)^N)*∑' k : ℕ, B (k+N) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left htail (by positivity)

theorem phaseBinomial_remainder_exponential_bound {r : ℝ} (hr : 0≤r) (hr4 : r≤1/4)
    (t : ℝ) (x : ℂ) (hx : ‖x‖≤r) (N : ℕ) :
    ‖(1+x)^(-(t:ℂ)*I)-∑ k∈Finset.range N,
      phaseBinomialCoefficient (-(t:ℂ)*I) k*x^k‖≤
        (1/(2:ℝ)^N)*Real.exp (4*|t| * r) := by
  have hbase : 0<1-2*r := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hbase
  have hfrac : (1-2*r)⁻¹-1≤4*r := by
    apply (sub_le_iff_le_add).mpr
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hbase).mpr
    nlinarith
  have hl : -Real.log (1-2*r)≤4*r := by linarith
  have he : (1-2*r)^(-|t|)≤Real.exp (4*|t| * r) := by
    rw [Real.rpow_def_of_pos hbase]
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg t]
  exact (phaseBinomial_remainder_bound hr (by linarith) t x hx N).trans
    (mul_le_mul_of_nonneg_left he (by positivity))

end
end Sechstmoment
