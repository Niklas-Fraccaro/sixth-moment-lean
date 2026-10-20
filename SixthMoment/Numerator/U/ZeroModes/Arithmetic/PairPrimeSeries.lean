import Mathlib.Analysis.SpecificLimits.Normed
import SixthMoment.Numerator.U.Diagonal.DiagonalEulerCoefficients


namespace SixthMoment
open scoped BigOperators
open ArithmeticFunction

noncomputable section
set_option maxHeartbeats 0

def pairPrimePowerCoefficient (a b : ℂ) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (n+1), a^i*b^(n-i)

@[simp] theorem pairPrimePowerCoefficient_zero (a b : ℂ) :
    pairPrimePowerCoefficient a b 0 = 1 := by
  simp [pairPrimePowerCoefficient]

def shiftedPairArithmetic (a b : ℂ) : ArithmeticFunction ℂ :=
  shiftedPowerArithmetic a * shiftedPowerArithmetic b

theorem shiftedPairArithmetic_multiplicative (a b : ℂ) :
    (shiftedPairArithmetic a b).IsMultiplicative :=
  (shiftedPowerArithmetic_multiplicative a).mul
    (shiftedPowerArithmetic_multiplicative b)

theorem shiftedPairArithmetic_primePower {p : ℕ} (hp : Nat.Prime p)
    (a b : ℂ) (n : ℕ) :
    shiftedPairArithmetic a b (p^n) =
      pairPrimePowerCoefficient ((p:ℂ)^(-a)) ((p:ℂ)^(-b)) n := by
  rw [shiftedPairArithmetic, arithmeticConvolution_primePower hp]
  simp_rw [shiftedPowerArithmetic_primePower hp]
  rfl

theorem pairPrimePowerCoefficient_succ (a b : ℂ) (n : ℕ) :
    pairPrimePowerCoefficient a b (n+1) =
      a*pairPrimePowerCoefficient a b n+b^(n+1) := by
  unfold pairPrimePowerCoefficient
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_succ]
  ring

theorem pairPrimePowerCoefficient_add (a b : ℂ) (j ν : ℕ) :
    pairPrimePowerCoefficient a b (j+ν) =
      a^ν*pairPrimePowerCoefficient a b j+
        b^(j+1)*(∑ k ∈ Finset.range ν, a^k*b^(ν-1-k)) := by
  induction ν with
  | zero => simp
  | succ ν ih =>
      rw [Nat.add_succ, pairPrimePowerCoefficient_succ, ih]
      rw [Finset.sum_range_succ']
      simp only [pow_zero, one_mul, Nat.succ_sub_succ_eq_sub,
        Nat.sub_zero]
      have hsum : (∑ k ∈ Finset.range ν, a^(k+1)*b^(ν-(k+1))) =
          a*(∑ k ∈ Finset.range ν, a^k*b^(ν-1-k)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        have he : ν-(k+1)=ν-1-k := by omega
        rw [he, pow_succ]
        ring
      rw [hsum, pow_succ]
      rw [show j+ν+1=(j+1)+ν by omega, pow_add]
      ring

theorem pairPrimePowerCoefficient_norm_le {a b : ℂ} {M : ℝ}
    (hM : 0 ≤ M) (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (n : ℕ) :
    ‖pairPrimePowerCoefficient a b n‖ ≤ (n+1:ℝ)*M^n := by
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), ‖a^i*b^(n-i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), M^n := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
      rw [norm_mul, Complex.norm_pow, Complex.norm_pow]
      calc
        _ ≤ M^i*M^(n-i) := by gcongr
        _ = M^n := by rw [← pow_add, Nat.add_sub_of_le hi']
    _ = _ := by simp

private theorem pairPolynomialGeometric_summable {q : ℝ} (hq₀ : 0 ≤ q) (hq : q < 1) :
    Summable (fun n : ℕ => (n+1:ℝ)^2*q^n) := by
  have hqn : ‖q‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hq₀] using hq
  have h₂ := summable_pow_mul_geometric_of_norm_lt_one 2 hqn
  have h₁ := summable_pow_mul_geometric_of_norm_lt_one 1 hqn
  have h₀ := summable_geometric_of_norm_lt_one hqn
  apply ((h₂.add (h₁.mul_left 2)).add h₀).congr
  intro n
  simp only [pow_one]
  ring

theorem pairShiftedPrimeSeries_norm_summable {A D C B r : ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) (hD : ‖D‖ ≤ M)
    (hC : ‖C‖ ≤ M) (hB : ‖B‖ ≤ M) (hr : M^2*‖r‖ < 1) (ν : ℕ) :
    Summable (fun j : ℕ => ‖pairPrimePowerCoefficient A D j*
      pairPrimePowerCoefficient C B (j+ν)*r^j‖) := by
  have hs := (pairPolynomialGeometric_summable (by positivity) hr).mul_left
    ((ν+1:ℝ)*M^ν)
  apply hs.of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, norm_mul, Complex.norm_pow]
  calc
    _ ≤ ((j+1:ℝ)*M^j)*((j+ν+1:ℝ)*M^(j+ν))*‖r‖^j := by
      gcongr
      · exact pairPrimePowerCoefficient_norm_le hM hA hD j
      · simpa only [Nat.cast_add] using pairPrimePowerCoefficient_norm_le hM hC hB (j+ν)
    _ ≤ ((j+1:ℝ)*M^j)*(((ν+1:ℝ)*(j+1:ℝ))*M^(j+ν))*‖r‖^j := by
      gcongr
      have : (0:ℝ) ≤ (ν:ℝ)*(j:ℝ) := by positivity
      nlinarith
    _ = _ := by
      rw [pow_add, mul_pow]
      rw [show (M^2)^j = (M^j)^2 by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring

theorem pairPrimeGeneratingSeries_norm_summable {A D x : ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) (hD : ‖D‖ ≤ M) (hx : M*‖x‖ < 1) :
    Summable (fun j : ℕ => ‖pairPrimePowerCoefficient A D j*x^j‖) := by
  apply (pairPolynomialGeometric_summable (by positivity) hx).of_norm_bounded
  intro j
  rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_pow]
  calc
    _ ≤ ((j+1:ℝ)*M^j)*‖x‖^j := by
      gcongr
      exact pairPrimePowerCoefficient_norm_le hM hA hD j
    _ ≤ (j+1:ℝ)^2*(M*‖x‖)^j := by
      rw [mul_pow]
      have hj : (j+1:ℝ) ≤ (j+1:ℝ)^2 := by
        have := Nat.cast_nonneg (α := ℝ) j
        nlinarith
      have hm : 0 ≤ M^j*‖x‖^j := by positivity
      calc
        _ = (j+1:ℝ)*(M^j*‖x‖^j) := by ring
        _ ≤ (j+1:ℝ)^2*(M^j*‖x‖^j) := mul_le_mul_of_nonneg_right hj hm
        _ = _ := by ring

def pairDiagonalPrimeSeries (A D C B r : ℂ) : ℂ :=
  ∑' j : ℕ, pairPrimePowerCoefficient A D j*
    pairPrimePowerCoefficient C B j*r^j

def pairShiftedPrimeSeries (A D C B r : ℂ) (ν : ℕ) : ℂ :=
  ∑' j : ℕ, pairPrimePowerCoefficient A D j*
    pairPrimePowerCoefficient C B (j+ν)*r^j

def pairPrimeGeneratingSeries (A D x : ℂ) : ℂ :=
  ∑' j : ℕ, pairPrimePowerCoefficient A D j*x^j

private theorem pairGeneratingRationalAlgebra (a d G : ℂ)
    (ha : 1-a ≠ 0) (hd : 1-d ≠ 0)
    (h : G=1+(a*G+d*(1-d)⁻¹)) : G=1/((1-a)*(1-d)) := by
  apply (eq_div_iff (mul_ne_zero ha hd)).mpr
  field_simp [hd] at h
  linear_combination h

theorem pairPrimeGeneratingSeries_closed (A D x : ℂ)
    (hs : Summable (fun j : ℕ => ‖pairPrimePowerCoefficient A D j*x^j‖))
    (hA : 1-A*x ≠ 0) (hD : ‖D*x‖ < 1) :
    pairPrimeGeneratingSeries A D x = 1/((1-A*x)*(1-D*x)) := by
  have hg := summable_geometric_of_norm_lt_one hD
  have hDn : 1-D*x ≠ 0 := by
    intro he
    have he' : D*x=1 := by linear_combination -he
    rw [he', norm_one] at hD
    exact (lt_irrefl (1:ℝ)) hD
  have hterm (j : ℕ) : pairPrimePowerCoefficient A D (j+1)*x^(j+1) =
      (A*x)*(pairPrimePowerCoefficient A D j*x^j)+(D*x)*(D*x)^j := by
    rw [pairPrimePowerCoefficient_succ, pow_succ, pow_succ, mul_pow]
    ring
  have he := hs.of_norm.tsum_eq_zero_add
  simp only [pairPrimePowerCoefficient_zero, pow_zero, one_mul] at he
  simp_rw [hterm] at he
  rw [Summable.tsum_add (hs.of_norm.mul_left _) (hg.mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_geometric_of_norm_lt_one hD] at he
  change pairPrimeGeneratingSeries A D x =
    1+((A*x)*pairPrimeGeneratingSeries A D x+(D*x)*(1-D*x)⁻¹) at he
  exact pairGeneratingRationalAlgebra (A*x) (D*x)
    (pairPrimeGeneratingSeries A D x) hA hDn he

private theorem pairWeightProduct_norm_lt_one {U V r : ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hU : ‖U‖ ≤ M) (hV : ‖V‖ ≤ M) (hr : M^2*‖r‖ < 1) :
    ‖U*V*r‖ < 1 := by
  calc
    _ = ‖U‖*‖V‖*‖r‖ := by rw [norm_mul, norm_mul]
    _ ≤ M*M*‖r‖ := by gcongr
    _ = M^2*‖r‖ := by ring
    _ < 1 := hr

private theorem pairOneSub_ne_zero {x : ℂ} (hx : ‖x‖ < 1) : 1-x ≠ 0 := by
  intro he
  have he' : x=1 := by linear_combination -he
  rw [he', norm_one] at hx
  exact (lt_irrefl (1:ℝ)) hx

private theorem pairDiagonalRationalAlgebra (x y z w S : ℂ)
    (hx : 1-x ≠ 0) (hy : 1-y ≠ 0) (hz : 1-z ≠ 0) (hw : 1-w ≠ 0)
    (h : S = 1+x*S+y/((1-y)*(1-w))+z/((1-z)*(1-w))+w/(1-w)) :
    S = (1-y*z)/((1-x)*(1-y)*(1-z)*(1-w)) := by
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero hx hy) hz) hw)).mpr
  field_simp [hy, hz, hw] at h
  linear_combination h

theorem pairDiagonalPrimeSeries_closed {A D C B r : ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) (hD : ‖D‖ ≤ M)
    (hC : ‖C‖ ≤ M) (hB : ‖B‖ ≤ M) (hr : M^2*‖r‖ < 1) :
    pairDiagonalPrimeSeries A D C B r =
      (1-A*B*C*D*r^2)/((1-A*C*r)*(1-A*B*r)*(1-C*D*r)*(1-B*D*r)) := by
  have hAC := pairWeightProduct_norm_lt_one hM hA hC hr
  have hAB := pairWeightProduct_norm_lt_one hM hA hB hr
  have hCD := pairWeightProduct_norm_lt_one hM hC hD hr
  have hBD := pairWeightProduct_norm_lt_one hM hB hD hr
  have hACn := pairOneSub_ne_zero hAC
  have hABn := pairOneSub_ne_zero hAB
  have hCDn := pairOneSub_ne_zero hCD
  have hBDn := pairOneSub_ne_zero hBD
  have hBr : M*‖B*r‖ < 1 := by
    calc
      _ = M*(‖B‖*‖r‖) := by rw [norm_mul]
      _ ≤ M*(M*‖r‖) := by gcongr
      _ = M^2*‖r‖ := by ring
      _ < 1 := hr
  have hDr : M*‖D*r‖ < 1 := by
    calc
      _ = M*(‖D‖*‖r‖) := by rw [norm_mul]
      _ ≤ M*(M*‖r‖) := by gcongr
      _ = M^2*‖r‖ := by ring
      _ < 1 := hr
  have hd : Summable (fun j : ℕ => ‖pairPrimePowerCoefficient A D j*
      pairPrimePowerCoefficient C B j*r^j‖) := by
    simpa using pairShiftedPrimeSeries_norm_summable hM hA hD hC hB hr 0
  have h₁ := pairPrimeGeneratingSeries_norm_summable hM hA hD hBr
  have h₂ := pairPrimeGeneratingSeries_norm_summable hM hC hB hDr
  have hg := summable_geometric_of_norm_lt_one hBD
  have hG₁ := pairPrimeGeneratingSeries_closed A D (B*r) h₁
    (by simpa only [mul_assoc] using hABn) (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hBD)
  have hG₂ := pairPrimeGeneratingSeries_closed C B (D*r) h₂
    (by simpa only [mul_assoc] using hCDn) (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hBD)
  have hterm (j : ℕ) :
      pairPrimePowerCoefficient A D (j+1)*pairPrimePowerCoefficient C B (j+1)*r^(j+1) =
      (A*C*r)*(pairPrimePowerCoefficient A D j*pairPrimePowerCoefficient C B j*r^j)+
      (A*B*r)*(pairPrimePowerCoefficient A D j*(B*r)^j)+
      (C*D*r)*(pairPrimePowerCoefficient C B j*(D*r)^j)+
      (B*D*r)*(B*D*r)^j := by
    rw [pairPrimePowerCoefficient_succ, pairPrimePowerCoefficient_succ]
    simp only [pow_succ, mul_pow]
    ring
  have he := hd.of_norm.tsum_eq_zero_add
  simp only [pairPrimePowerCoefficient_zero, pow_zero, one_mul] at he
  simp_rw [hterm] at he
  rw [Summable.tsum_add
      (((hd.of_norm.mul_left _).add (h₁.of_norm.mul_left _)).add (h₂.of_norm.mul_left _))
      (hg.mul_left _),
    Summable.tsum_add ((hd.of_norm.mul_left _).add (h₁.of_norm.mul_left _))
      (h₂.of_norm.mul_left _),
    Summable.tsum_add (hd.of_norm.mul_left _) (h₁.of_norm.mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_norm_lt_one hBD] at he
  change pairDiagonalPrimeSeries A D C B r =
    1+((A*C*r)*pairDiagonalPrimeSeries A D C B r+
      (A*B*r)*pairPrimeGeneratingSeries A D (B*r)+
      (C*D*r)*pairPrimeGeneratingSeries C B (D*r)+
      (B*D*r)*(1-B*D*r)⁻¹) at he
  rw [hG₁,hG₂] at he
  have halg : pairDiagonalPrimeSeries A D C B r =
      1+(A*C*r)*pairDiagonalPrimeSeries A D C B r+
        (A*B*r)/((1-A*B*r)*(1-B*D*r))+
        (C*D*r)/((1-C*D*r)*(1-B*D*r))+(B*D*r)/(1-B*D*r) := by
    convert he using 1; simp only [div_eq_mul_inv]; ring
  have hclosed := pairDiagonalRationalAlgebra (A*C*r) (A*B*r) (C*D*r) (B*D*r)
    (pairDiagonalPrimeSeries A D C B r) hACn hABn hCDn hBDn halg
  convert hclosed using 1; congr 1; ring

theorem pairShiftedPrimeSeries_recurrence (A D C B r : ℂ) (ν : ℕ)
    (hdiag : Summable (fun j : ℕ => ‖pairPrimePowerCoefficient A D j*
      pairPrimePowerCoefficient C B j*r^j‖))
    (haux : Summable (fun j : ℕ => ‖pairPrimePowerCoefficient A D j*(B*r)^j‖)) :
    pairShiftedPrimeSeries A D C B r ν =
      C^ν*pairDiagonalPrimeSeries A D C B r+
        B*(∑ k ∈ Finset.range ν, C^k*B^(ν-1-k))*
          pairPrimeGeneratingSeries A D (B*r) := by
  let K := ∑ k ∈ Finset.range ν, C^k*B^(ν-1-k)
  have hterm (j : ℕ) :
      pairPrimePowerCoefficient A D j*pairPrimePowerCoefficient C B (j+ν)*r^j =
      C^ν*(pairPrimePowerCoefficient A D j*pairPrimePowerCoefficient C B j*r^j)+
        (B*K)*(pairPrimePowerCoefficient A D j*(B*r)^j) := by
    rw [pairPrimePowerCoefficient_add, pow_succ, mul_pow]
    dsimp [K]
    ring
  unfold pairShiftedPrimeSeries pairDiagonalPrimeSeries pairPrimeGeneratingSeries
  simp_rw [hterm]
  rw [Summable.tsum_add (hdiag.of_norm.mul_left _) (haux.of_norm.mul_left _),
    tsum_mul_left, tsum_mul_left]

private theorem pairShiftedRatioAlgebra (x y z w c k S G N : ℂ)
    (hx : 1-x ≠ 0) (hy : 1-y ≠ 0) (hz : 1-z ≠ 0) (hw : 1-w ≠ 0)
    (hnum : 1-y*z ≠ 0)
    (hS : S=(1-y*z)/((1-x)*(1-y)*(1-z)*(1-w)))
    (hG : G=1/((1-y)*(1-w))) (hN : N=c*S+k*G) :
    N/S=c+k*(1-x)*(1-z)/(1-y*z) := by
  have hSn : S ≠ 0 := by
    rw [hS]
    exact div_ne_zero hnum (mul_ne_zero (mul_ne_zero (mul_ne_zero hx hy) hz) hw)
  have hGS : G/S=(1-x)*(1-z)/(1-y*z) := by
    rw [hG,hS]
    field_simp [hx,hy,hz,hw,hnum]
  calc
    N/S = (c*S+k*G)/S := by rw [hN]
    _ = c+k*(G/S) := by field_simp [hSn]
    _ = _ := by rw [hGS]; ring

theorem pairShiftedPrimeSeries_ratio {A D C B r : ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) (hD : ‖D‖ ≤ M)
    (hC : ‖C‖ ≤ M) (hB : ‖B‖ ≤ M) (hr : M^2*‖r‖ < 1) (ν : ℕ) :
    pairShiftedPrimeSeries A D C B r ν / pairDiagonalPrimeSeries A D C B r =
      C^ν+B*(∑ k ∈ Finset.range ν, C^k*B^(ν-1-k))*
        (1-A*C*r)*(1-C*D*r)/(1-A*B*C*D*r^2) := by
  have hAC := pairWeightProduct_norm_lt_one hM hA hC hr
  have hAB := pairWeightProduct_norm_lt_one hM hA hB hr
  have hCD := pairWeightProduct_norm_lt_one hM hC hD hr
  have hBD := pairWeightProduct_norm_lt_one hM hB hD hr
  have hACn := pairOneSub_ne_zero hAC
  have hABn := pairOneSub_ne_zero hAB
  have hCDn := pairOneSub_ne_zero hCD
  have hBDn := pairOneSub_ne_zero hBD
  have hprod : ‖(A*C*r)*(B*D*r)‖ < 1 := by
    rw [norm_mul]
    calc
      ‖A*C*r‖*‖B*D*r‖ ≤ ‖A*C*r‖*1 :=
        mul_le_mul_of_nonneg_left hBD.le (norm_nonneg _)
      _ < 1 := by simpa using hAC
  have hnum : 1-(A*B*r)*(C*D*r) ≠ 0 := by
    convert pairOneSub_ne_zero hprod using 1; ring
  have hBr : M*‖B*r‖ < 1 := by
    calc
      _ = M*(‖B‖*‖r‖) := by rw [norm_mul]
      _ ≤ M*(M*‖r‖) := by gcongr
      _ = M^2*‖r‖ := by ring
      _ < 1 := hr
  have hd : Summable (fun j : ℕ => ‖pairPrimePowerCoefficient A D j*
      pairPrimePowerCoefficient C B j*r^j‖) := by
    simpa using pairShiftedPrimeSeries_norm_summable hM hA hD hC hB hr 0
  have h₁ := pairPrimeGeneratingSeries_norm_summable hM hA hD hBr
  have hG := pairPrimeGeneratingSeries_closed A D (B*r) h₁
    (by simpa only [mul_assoc] using hABn) (by simpa only [mul_assoc, mul_left_comm, mul_comm] using hBD)
  have hN := pairShiftedPrimeSeries_recurrence A D C B r ν hd h₁
  have hS := pairDiagonalPrimeSeries_closed hM hA hD hC hB hr
  have hS' : pairDiagonalPrimeSeries A D C B r =
      (1-(A*B*r)*(C*D*r))/((1-A*C*r)*(1-A*B*r)*(1-C*D*r)*(1-B*D*r)) := by
    rw [hS]
    congr 1
    ring
  have hG' : pairPrimeGeneratingSeries A D (B*r)=1/((1-A*B*r)*(1-B*D*r)) := by
    rw [hG]
    congr 2 <;> ring
  have he := pairShiftedRatioAlgebra (A*C*r) (A*B*r) (C*D*r) (B*D*r)
    (C^ν) (B*(∑ k ∈ Finset.range ν, C^k*B^(ν-1-k)))
    (pairDiagonalPrimeSeries A D C B r) (pairPrimeGeneratingSeries A D (B*r))
    (pairShiftedPrimeSeries A D C B r ν) hACn hABn hCDn hBDn hnum hS' hG' hN
  convert he using 1
  congr 2
  ring

theorem pairDiagonalPrimeSeries_ne_zero {A D C B r : ℂ} {M : ℝ}
    (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) (hD : ‖D‖ ≤ M)
    (hC : ‖C‖ ≤ M) (hB : ‖B‖ ≤ M) (hr : M^2*‖r‖ < 1) :
    pairDiagonalPrimeSeries A D C B r ≠ 0 := by
  have hAC := pairWeightProduct_norm_lt_one hM hA hC hr
  have hAB := pairWeightProduct_norm_lt_one hM hA hB hr
  have hCD := pairWeightProduct_norm_lt_one hM hC hD hr
  have hBD := pairWeightProduct_norm_lt_one hM hB hD hr
  have hprod : ‖(A*C*r)*(B*D*r)‖ < 1 := by
    rw [norm_mul]
    calc
      ‖A*C*r‖*‖B*D*r‖ ≤ ‖A*C*r‖*1 :=
        mul_le_mul_of_nonneg_left hBD.le (norm_nonneg _)
      _ < 1 := by simpa using hAC
  have hnum : 1-A*B*C*D*r^2 ≠ 0 := by
    convert pairOneSub_ne_zero hprod using 1
    congr 1
    ring
  rw [pairDiagonalPrimeSeries_closed hM hA hD hC hB hr]
  exact div_ne_zero hnum (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (pairOneSub_ne_zero hAC) (pairOneSub_ne_zero hAB))
      (pairOneSub_ne_zero hCD)) (pairOneSub_ne_zero hBD))

end
end SixthMoment
