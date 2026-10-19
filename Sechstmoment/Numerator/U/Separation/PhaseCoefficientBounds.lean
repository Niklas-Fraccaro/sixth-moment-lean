import Sechstmoment.Numerator.U.Separation.SeparatedGapKernel

/-! Genuine support and norm control of the separated coefficients.
No structural source hypothesis or desired moment estimate is added. -/
namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phaseAdjustedBeta_support (q : QuadraticScales) (β : ℕ → ℂ)
    (hs : ∀ b : ℕ, (b:ℝ)∉Icc q.B (2*q.B) → β b=0) (k : ℕ) :
    ∀ b : ℕ, (b:ℝ)∉Icc q.B (2*q.B) → phaseAdjustedBeta q β k b=0 := by
  intro b hb
  simp only [phaseAdjustedBeta,hs b hb,zero_mul]

theorem phaseAdjustedBeta_norm_le (q : QuadraticScales) (hB : 0<q.B)
    (β : ℕ → ℂ) (hs : ∀ b : ℕ, (b:ℝ)∉Icc q.B (2*q.B) → β b=0)
    (k b : ℕ) : ‖phaseAdjustedBeta q β k b‖≤‖β b‖ := by
  by_cases hb : (b:ℝ)∈Icc q.B (2*q.B)
  · have hx : 1≤(b:ℝ)/q.B := (le_div_iff₀ hB).mpr (by simpa using hb.1)
    have hxp : 0<(b:ℝ)/q.B := zero_lt_one.trans_le hx
    have hp : ‖(((b:ℝ)/q.B):ℂ)^(-(k:ℂ))‖≤1 := by
      rw [← Complex.ofReal_div]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hxp]
      simp only [Complex.neg_re,Complex.natCast_re]
      calc
        _ ≤ ((b:ℝ)/q.B)^(0:ℝ) := Real.rpow_le_rpow_of_exponent_le hx
          (neg_nonpos.mpr (Nat.cast_nonneg k))
        _ = _ := Real.rpow_zero _
    simpa only [phaseAdjustedBeta,norm_mul,mul_one] using
      mul_le_mul_of_nonneg_left hp (norm_nonneg (β b))
  · simp only [phaseAdjustedBeta,hs b hb,zero_mul,norm_zero,le_refl]

theorem phaseAdjustedBeta_source_bound (q : QuadraticScales) (hB : 0<q.B)
    (β : ℕ → ℂ) (hs : ∀ b : ℕ, (b:ℝ)∉Icc q.B (2*q.B) → β b=0)
    {K ε : ℝ} (hb : ∀ b : ℕ, ‖β b‖≤K*q.B^ε) (k : ℕ) :
    ∀ b : ℕ, ‖phaseAdjustedBeta q β k b‖≤K*q.B^ε :=
  fun b => (phaseAdjustedBeta_norm_le q hB β hs k b).trans (hb b)

theorem phaseBinomial_finite_coefficient_mass {r : ℝ} (hr : 0≤r) (hr1 : r<1)
    (t : ℝ) (x : ℂ) (hx : ‖x‖≤r) (N : ℕ) :
    (∑ k∈Finset.range N, ‖phaseBinomialCoefficient (-(t:ℂ)*I) k*x^k‖)≤
      (1-r)^(-|t|) := by
  have hs := phaseBinomialMajorant_hasSum (abs_nonneg t) hr hr1
  have hn (k : ℕ) : 0≤phaseBinomialMajorant |t| k*r^k :=
    mul_nonneg (phaseBinomialMajorant_nonneg (abs_nonneg t) k) (pow_nonneg hr k)
  calc
    _ ≤ ∑ k∈Finset.range N, phaseBinomialMajorant |t| k*r^k := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul,norm_pow]
      exact mul_le_mul (phaseBinomialCoefficient_imaginary_norm_le t k)
        (pow_le_pow_left₀ (norm_nonneg x) hx k) (by positivity)
        (phaseBinomialMajorant_nonneg (abs_nonneg t) k)
    _ ≤ ∑' k : ℕ, phaseBinomialMajorant |t| k*r^k :=
      hs.summable.sum_le_tsum (Finset.range N) (fun k _ => hn k)
    _ = _ := hs.tsum_eq

theorem phaseBinomial_finite_coefficient_mass_power {θ : ℝ} (_hθ : 0≤θ)
    {T : ℝ} (hT : 1≤T) {r : ℝ} (hr : 0≤r) (hr2 : r≤1/2)
    (hTr : T*r≤θ*Real.log T) (t : ℝ) (ht : |t|≤2*T)
    (x : ℂ) (hx : ‖x‖≤r) (N : ℕ) :
    (∑ k∈Finset.range N, ‖phaseBinomialCoefficient (-(t:ℂ)*I) k*x^k‖)≤T^(4*θ) := by
  have hbase : 0<1-r := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hbase
  have hfrac : (1-r)⁻¹-1≤2*r := by
    apply (sub_le_iff_le_add).mpr
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hbase).mpr
    nlinarith
  have hl : -Real.log (1-r)≤2*r := by linarith
  have he : (1-r)^(-|t|)≤Real.exp (2*|t| * r) := by
    rw [Real.rpow_def_of_pos hbase]
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg t]
  have hb : 2*|t| * r≤Real.log T*(4*θ) := by
    have h := mul_le_mul_of_nonneg_right ht hr
    nlinarith
  calc
    _ ≤ (1-r)^(-|t|) := phaseBinomial_finite_coefficient_mass hr (by linarith) t x hx N
    _ ≤ Real.exp (2*|t| * r) := he
    _ ≤ Real.exp (Real.log T*(4*θ)) := Real.exp_le_exp.mpr hb
    _ = _ := (Real.rpow_def_of_pos (zero_lt_one.trans_le hT) _).symm

theorem phaseSeparationScalar_finite_mass {θ : ℝ} (hθ : 0≤θ)
    {T : ℝ} (hT : 1≤T) (q : QuadraticScales) (sign t : ℝ)
    {r : ℝ} (hr : 0≤r) (hr2 : r≤1/2) (hTr : T*r≤θ*Real.log T)
    (ht : |t|≤2*T) (hx : |sign*2*q.H/(q.B*q.N₁*q.N₂)|≤r) (N : ℕ) :
    (∑ k∈Finset.range N, ‖phaseSeparationScalar q sign t k‖)≤T^(4*θ) := by
  exact phaseBinomial_finite_coefficient_mass_power hθ hT hr hr2 hTr t ht _
    (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx) N

end
end Sechstmoment
