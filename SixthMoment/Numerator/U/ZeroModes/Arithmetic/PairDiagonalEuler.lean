import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing
import SixthMoment.Numerator.U.Diagonal.DiagonalEulerSummability
import SixthMoment.Numerator.U.ZeroModes.Arithmetic.EtaResidueArithmetic


namespace SixthMoment
open ArithmeticFunction Nat Complex
open scoped BigOperators

set_option maxHeartbeats 0
noncomputable section

def shiftedPairDiagonalArithmetic (a b c d s : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => shiftedPairArithmetic a b n*shiftedPairArithmetic c d n*
    shiftedPowerArithmetic s n, by simp⟩

theorem shiftedPairDiagonalArithmetic_multiplicative (a b c d s : ℂ) :
    (shiftedPairDiagonalArithmetic a b c d s).IsMultiplicative := by
  have hab := shiftedPairArithmetic_multiplicative a b
  have hcd := shiftedPairArithmetic_multiplicative c d
  have hs := shiftedPowerArithmetic_multiplicative s
  constructor
  · simp only [shiftedPairDiagonalArithmetic, ArithmeticFunction.coe_mk]
    rw [hab.map_one, hcd.map_one, hs.map_one, mul_one, mul_one]
  · intro m n hmn
    simp only [shiftedPairDiagonalArithmetic, ArithmeticFunction.coe_mk]
    rw [hab.map_mul_of_coprime hmn, hcd.map_mul_of_coprime hmn, hs.map_mul_of_coprime hmn]
    ring

theorem shiftedPairDiagonalArithmetic_primePower {p : ℕ} (hp : p.Prime)
    (a b c d : ℂ) (m : ℕ) :
    shiftedPairDiagonalArithmetic a b c d 1 (p^m) =
      pairPrimePowerCoefficient ((p:ℂ)^(-a)) ((p:ℂ)^(-b)) m*
      pairPrimePowerCoefficient ((p:ℂ)^(-c)) ((p:ℂ)^(-d)) m*(1/(p:ℂ))^m := by
  simp only [shiftedPairDiagonalArithmetic, ArithmeticFunction.coe_mk,
    shiftedPairArithmetic_primePower hp, shiftedPowerArithmetic_primePower hp,
    Complex.cpow_neg_one, one_div]

theorem pairDivisorCoefficient_sq_le_ninth (m : ℕ) :
    (m+1:ℝ)^2 ≤ ((m+8).choose 8 : ℝ) := by
  have h₁ : m+1 ≤ d3PrimePowerCoefficient m := by
    change m+1 ≤ (m+1+1).choose (1+1)
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    omega
  have h₂ : (m+1:ℝ) ≤ (d3PrimePowerCoefficient m:ℝ) := by exact_mod_cast h₁
  exact (pow_le_pow_left₀ (by positivity) h₂ 2).trans
    (d3PrimePowerCoefficient_sq_le_d9_real m)

theorem shiftedPairDiagonalArithmetic_primePower_norm_le {e : ℝ}
    (a b c d : ℂ) (ha : e ≤ a.re) (hb : e ≤ b.re) (hc : e ≤ c.re) (hd : e ≤ d.re)
    (p : Nat.Primes) (m : ℕ) :
    ‖shiftedPairDiagonalArithmetic a b c d 1 (p.val^m)‖ ≤
      ‖diagonalNinthDivisorMajorant e (p.val^m)‖ := by
  have hp : (0:ℝ)<p.val := by exact_mod_cast p.property.pos
  have hweight (z : ℂ) (hz : e ≤ z.re) : ‖(p.val:ℂ)^(-z)‖ ≤ (p.val:ℝ)^(-e) := by
    apply bblrPrimePowerNorm_le p.property
    simp only [Complex.neg_re]
    linarith
  have hM : 0 ≤ (p.val:ℝ)^(-e) := Real.rpow_nonneg hp.le _
  have he : ((p.val:ℝ)^(-e))^2*‖1/(p.val:ℂ)‖ = (p.val:ℝ)^(-(1+2*e)) := by
    rw [primePolarGeometricRadius p (-e)]
    congr 1
    ring
  rw [shiftedPairDiagonalArithmetic_primePower p.property,
    diagonalNinthDivisorMajorant_primePower_norm, norm_mul, norm_mul, Complex.norm_pow]
  calc
    _ ≤ ((m+1:ℝ)*((p.val:ℝ)^(-e))^m)*
        ((m+1:ℝ)*((p.val:ℝ)^(-e))^m)*‖1/(p.val:ℂ)‖^m := by
      gcongr
      · exact pairPrimePowerCoefficient_norm_le hM (hweight a ha) (hweight b hb) m
      · exact pairPrimePowerCoefficient_norm_le hM (hweight c hc) (hweight d hd) m
    _ = (m+1:ℝ)^2*(((p.val:ℝ)^(-e))^2*‖1/(p.val:ℂ)‖)^m := by
      rw [mul_pow]
      rw [show (((p.val:ℝ)^(-e))^2)^m=(((p.val:ℝ)^(-e))^m)^2 by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring
    _ ≤ _ := by
      rw [he]
      exact mul_le_mul_of_nonneg_right (pairDivisorCoefficient_sq_le_ninth m)
        (by positivity)

theorem shiftedPairDiagonalArithmetic_norm_summable {e : ℝ} (he : 0 < e)
    (a b c d : ℂ) (ha : e ≤ a.re) (hb : e ≤ b.re) (hc : e ≤ c.re) (hd : e ≤ d.re) :
    Summable (fun n => ‖shiftedPairDiagonalArithmetic a b c d 1 n‖) := by
  apply (diagonalNinthDivisorMajorant_norm_summable he).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  exact multiplicative_norm_le_of_primePower (shiftedPairDiagonalArithmetic_multiplicative _ _ _ _ _)
    (diagonalNinthDivisorMajorant_multiplicative _)
    (fun p m => shiftedPairDiagonalArithmetic_primePower_norm_le a b c d ha hb hc hd p m) n

theorem shiftedPairDiagonalArithmetic_euler_hasProd {e : ℝ} (he : 0 < e)
    (a b c d : ℂ) (ha : e ≤ a.re) (hb : e ≤ b.re) (hc : e ≤ c.re) (hd : e ≤ d.re) :
    HasProd (fun p : Nat.Primes => pairDiagonalPrimeSeries
      ((p.val:ℂ)^(-a)) ((p.val:ℂ)^(-b)) ((p.val:ℂ)^(-c)) ((p.val:ℂ)^(-d)) (1/(p.val:ℂ)))
      (∑' n, shiftedPairDiagonalArithmetic a b c d 1 n) := by
  have h := (shiftedPairDiagonalArithmetic_multiplicative a b c d 1).eulerProduct_hasProd
    (shiftedPairDiagonalArithmetic_norm_summable he a b c d ha hb hc hd)
  apply h.congr_fun
  intro p
  unfold pairDiagonalPrimeSeries
  apply tsum_congr
  intro m
  exact (shiftedPairDiagonalArithmetic_primePower p.property a b c d m).symm

theorem shiftedPairDiagonalPrimeSeries_closed {e : ℝ} (he : 0 < e)
    (a b c d : ℂ) (ha : e ≤ a.re) (hb : e ≤ b.re) (hc : e ≤ c.re) (hd : e ≤ d.re)
    (p : Nat.Primes) :
    pairDiagonalPrimeSeries ((p.val:ℂ)^(-a)) ((p.val:ℂ)^(-b))
      ((p.val:ℂ)^(-c)) ((p.val:ℂ)^(-d)) (1/(p.val:ℂ)) =
      (1-(p.val:ℂ)^(-(2+a+b+c+d))) /
        ((1-(p.val:ℂ)^(-(1+a+c)))*(1-(p.val:ℂ)^(-(1+a+d)))*
          (1-(p.val:ℂ)^(-(1+b+c)))*(1-(p.val:ℂ)^(-(1+b+d)))) := by
  have hp0 : (p.val:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hweight (z : ℂ) (hz : e ≤ z.re) : ‖(p.val:ℂ)^(-z)‖ ≤ (p.val:ℝ)^(-e) := by
    apply bblrPrimePowerNorm_le p.property
    simp only [Complex.neg_re]
    linarith
  have hr : ((p.val:ℝ)^(-e))^2*‖1/(p.val:ℂ)‖ < 1 := by
    rw [primePolarGeometricRadius p (-e)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt) (by linarith)
  rw [pairDiagonalPrimeSeries_closed (Real.rpow_nonneg (by positivity) _)
    (hweight a ha) (hweight b hb) (hweight c hc) (hweight d hd) hr]
  have hpair (z w : ℂ) : (p.val:ℂ)^(-z)*(p.val:ℂ)^(-w)*(1/(p.val:ℂ)) =
      (p.val:ℂ)^(-(1+z+w)) := by
    rw [one_div, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hp0,
      ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  have hprod : (p.val:ℂ)^(-a)*(p.val:ℂ)^(-d)*(p.val:ℂ)^(-c)*(p.val:ℂ)^(-b)*
      (1/(p.val:ℂ))^2 = (p.val:ℂ)^(-(2+a+b+c+d)) := by
    simp only [pow_two, one_div, ← Complex.cpow_neg_one]
    rw [← mul_assoc, ← Complex.cpow_add _ _ hp0, ← Complex.cpow_add _ _ hp0,
      ← Complex.cpow_add _ _ hp0, ← Complex.cpow_add _ _ hp0,
      ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  rw [hprod,hpair,hpair]
  have hbc : (p.val:ℂ)^(-c)*(p.val:ℂ)^(-b)*(1/(p.val:ℂ))=
      (p.val:ℂ)^(-(1+b+c)) := by rw [mul_comm ((p.val:ℂ)^(-c))]; exact hpair b c
  have hbd : (p.val:ℂ)^(-d)*(p.val:ℂ)^(-b)*(1/(p.val:ℂ))=
      (p.val:ℂ)^(-(1+b+d)) := by rw [mul_comm ((p.val:ℂ)^(-d))]; exact hpair b d
  rw [hbc,hbd]

theorem shiftedPairDiagonalPrimeSeries_zeta_hasProd {e : ℝ} (he : 0 < e)
    (a b c d : ℂ) (ha : e ≤ a.re) (hb : e ≤ b.re) (hc : e ≤ c.re) (hd : e ≤ d.re) :
    HasProd (fun p : Nat.Primes => pairDiagonalPrimeSeries
      ((p.val:ℂ)^(-a)) ((p.val:ℂ)^(-b)) ((p.val:ℂ)^(-c)) ((p.val:ℂ)^(-d)) (1/(p.val:ℂ)))
      (bblrAArithmetic a b c d) := by
  have h₁ := riemannZeta_eulerProduct_hasProd
    (show 1<(1+a+c).re by simp; linarith)
  have h₂ := riemannZeta_eulerProduct_hasProd
    (show 1<(1+a+d).re by simp; linarith)
  have h₃ := riemannZeta_eulerProduct_hasProd
    (show 1<(1+b+c).re by simp; linarith)
  have h₄ := riemannZeta_eulerProduct_hasProd
    (show 1<(1+b+d).re by simp; linarith)
  have hden : 1<(2+a+b+c+d).re := by simp; linarith
  have h₅ := (riemannZeta_eulerProduct_hasProd hden).inv₀
    (riemannZeta_ne_zero_of_one_le_re hden.le)
  simp only [inv_inv] at h₅
  have h := (((h₁.mul h₂).mul h₃).mul h₄).mul h₅
  have htarget : riemannZeta (1+a+c)*riemannZeta (1+a+d)*riemannZeta (1+b+c)*
      riemannZeta (1+b+d)*(riemannZeta (2+a+b+c+d))⁻¹=bblrAArithmetic a b c d := by
    rfl
  rw [htarget] at h
  apply h.congr_fun
  intro p
  rw [shiftedPairDiagonalPrimeSeries_closed he a b c d ha hb hc hd p]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem shiftedPairDiagonalArithmetic_eq_fourZeta {e : ℝ} (he : 0 < e)
    (a b c d : ℂ) (ha : e ≤ a.re) (hb : e ≤ b.re) (hc : e ≤ c.re) (hd : e ≤ d.re) :
    (∑' n, shiftedPairDiagonalArithmetic a b c d 1 n)=bblrAArithmetic a b c d :=
  (shiftedPairDiagonalArithmetic_euler_hasProd he a b c d ha hb hc hd).unique
    (shiftedPairDiagonalPrimeSeries_zeta_hasProd he a b c d ha hb hc hd)

theorem pairPrimePowerCoefficient_mul_weights (A B Z : ℂ) (n : ℕ) :
    pairPrimePowerCoefficient (A*Z) (B*Z) n = pairPrimePowerCoefficient A B n*Z^n := by
  unfold pairPrimePowerCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  simp only [mul_pow]
  rw [show A^j*Z^j*(B^(n-j)*Z^(n-j))=A^j*B^(n-j)*(Z^j*Z^(n-j)) by ring,
    ← pow_add, Nat.add_sub_of_le hjn]

theorem shiftedPairArithmetic_add_shifts (a b s : ℂ) :
    shiftedPairArithmetic (a+s) (b+s) =
      (shiftedPairArithmetic a b).pmul (shiftedPowerArithmetic s) := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (shiftedPairArithmetic_multiplicative _ _) _
    ((shiftedPairArithmetic_multiplicative _ _).pmul (shiftedPowerArithmetic_multiplicative _))).mpr
  intro p n hp
  rw [ArithmeticFunction.pmul_apply, shiftedPairArithmetic_primePower hp,
    shiftedPairArithmetic_primePower hp, shiftedPowerArithmetic_primePower hp]
  have hp0 : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hshift (z : ℂ) : (p:ℂ)^(-(z+s))=(p:ℂ)^(-z)*(p:ℂ)^(-s) := by
    rw [← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  rw [hshift,hshift,pairPrimePowerCoefficient_mul_weights]

theorem shiftedPairDiagonalArithmetic_add_shifts (a b c d s : ℂ) :
    shiftedPairDiagonalArithmetic (a+s) (b+s) (c+s) (d+s) 1 =
      shiftedPairDiagonalArithmetic a b c d (1+2*s) := by
  ext n
  by_cases hn : n=0
  · simp [hn]
  have hn0 : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn
  simp only [shiftedPairDiagonalArithmetic, ArithmeticFunction.coe_mk]
  rw [shiftedPairArithmetic_add_shifts, shiftedPairArithmetic_add_shifts]
  simp only [
    ArithmeticFunction.pmul_apply, shiftedPowerArithmetic_apply _ hn]
  have he : (n:ℂ)^(-s)*(n:ℂ)^(-s)*(n:ℂ)^(-1:ℂ)=(n:ℂ)^(-(1+2*s)) := by
    rw [← Complex.cpow_add _ _ hn0, ← Complex.cpow_add _ _ hn0]
    congr 1
    ring
  calc
    _ = shiftedPairArithmetic a b n*shiftedPairArithmetic c d n*
      ((n:ℂ)^(-s)*(n:ℂ)^(-s)*(n:ℂ)^(-1:ℂ)) := by ring
    _ = _ := by rw [he]

theorem shiftedPairDiagonalArithmetic_initial_norm_summable {α : MomentShifts}
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ 1/8) {s : ℂ} (hs : 1/4 ≤ s.re) :
    Summable (fun n => ‖shiftedPairDiagonalArithmetic (α 0) (α 1) (α 2) (α 3) (1+2*s) n‖) := by
  rw [← shiftedPairDiagonalArithmetic_add_shifts]
  have hre (j : Fin 4) : (1/8:ℝ) ≤ (α j+s).re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
    simp only [Complex.add_re]
    linarith
  exact shiftedPairDiagonalArithmetic_norm_summable (by norm_num : (0:ℝ)<1/8)
    _ _ _ _ (hre 0) (hre 1) (hre 2) (hre 3)

theorem shiftedPairDiagonalArithmetic_initial_eq_fourZeta {α : MomentShifts}
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ 1/8) {s : ℂ} (hs : 1/4 ≤ s.re) :
    (∑' n, shiftedPairDiagonalArithmetic (α 0) (α 1) (α 2) (α 3) (1+2*s) n) =
      bblrAArithmetic (α 0+s) (α 1+s) (α 2+s) (α 3+s) := by
  rw [← shiftedPairDiagonalArithmetic_add_shifts]
  have hre (j : Fin 4) : (1/8:ℝ) ≤ (α j+s).re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
    simp only [Complex.add_re]
    linarith
  exact shiftedPairDiagonalArithmetic_eq_fourZeta (by norm_num : (0:ℝ)<1/8)
    _ _ _ _ (hre 0) (hre 1) (hre 2) (hre 3)

end
end SixthMoment
