import Sechstmoment.Arithmetic.Euler.Shifted.Convergence
import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.EtaArithmetic
import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.PairPrimeSeries


namespace Sechstmoment
open ArithmeticFunction Nat Complex
open scoped BigOperators
open Classical

set_option maxHeartbeats 0
noncomputable section

def bblrBPrimeFactor (p : ℕ) (α β γ δ : ℂ) (ν : ℕ) : ℂ :=
  (∑' j : ℕ, shiftedPairArithmetic α β (p^j)*
    shiftedPairArithmetic γ δ (p^(j+ν))*(1/(p:ℂ))^j) /
  (∑' j : ℕ, shiftedPairArithmetic α β (p^j)*
    shiftedPairArithmetic γ δ (p^j)*(1/(p:ℂ))^j)

theorem bblrBPrimeFactor_eq_pairSeries {p : ℕ} (hp : p.Prime)
    (α β γ δ : ℂ) (ν : ℕ) :
    bblrBPrimeFactor p α β γ δ ν =
      pairShiftedPrimeSeries ((p:ℂ)^(-α)) ((p:ℂ)^(-β))
        ((p:ℂ)^(-γ)) ((p:ℂ)^(-δ)) (1/(p:ℂ)) ν /
      pairDiagonalPrimeSeries ((p:ℂ)^(-α)) ((p:ℂ)^(-β))
        ((p:ℂ)^(-γ)) ((p:ℂ)^(-δ)) (1/(p:ℂ)) := by
  unfold bblrBPrimeFactor pairShiftedPrimeSeries pairDiagonalPrimeSeries
  simp_rw [shiftedPairArithmetic_primePower hp]

theorem bblrEtaCorrection_eq_crossedPrimeFactor {p : ℕ} (hp : p.Prime)
    (α β γ δ : ℂ) :
    bblrEtaCorrection p (α+γ) (γ-δ) (α-β+γ-δ) =
      (1-(p:ℂ)^(-α)*(p:ℂ)^(-γ)*(1/(p:ℂ)))*
      (1-(p:ℂ)^(-γ)*(p:ℂ)^δ*(1/(p:ℂ))) /
      (1-(p:ℂ)^(-α)*(p:ℂ)^β*(p:ℂ)^(-γ)*(p:ℂ)^δ*(1/(p:ℂ))^2) := by
  have hp0 : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h₁ : (p:ℂ)^(-α)*(p:ℂ)^(-γ)*(1/(p:ℂ)) =
      (p:ℂ)^(-(1+(α+γ))) := by
    rw [one_div, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hp0,
      ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  have h₂ : (p:ℂ)^(-γ)*(p:ℂ)^δ*(1/(p:ℂ)) =
      (p:ℂ)^(-(1+(γ-δ))) := by
    rw [one_div, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ hp0,
      ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  have h₃ : (p:ℂ)^(-α)*(p:ℂ)^β*(p:ℂ)^(-γ)*(p:ℂ)^δ*(1/(p:ℂ))^2 =
      (p:ℂ)^(-(2+(α-β+γ-δ))) := by
    simp only [pow_two, one_div, ← Complex.cpow_neg_one]
    rw [← mul_assoc, ← Complex.cpow_add _ _ hp0, ← Complex.cpow_add _ _ hp0,
      ← Complex.cpow_add _ _ hp0, ← Complex.cpow_add _ _ hp0,
      ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  rw [h₁,h₂,h₃]
  rfl

theorem bblrEta_eq_B_primePower {p : ℕ} (hp : p.Prime)
    (α β γ δ : ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hα : ‖(p:ℂ)^(-α)‖ ≤ M) (hδ : ‖(p:ℂ)^δ‖ ≤ M)
    (hγ : ‖(p:ℂ)^(-γ)‖ ≤ M) (hβ : ‖(p:ℂ)^β‖ ≤ M)
    (hr : M^2*‖1/(p:ℂ)‖ < 1) (ν : ℕ) :
    bblrNormalizedEtaArithmetic α β γ δ 0 (p^ν) =
      bblrBPrimeFactor p α (-δ) γ (-β) ν := by
  rw [bblrNormalizedEtaArithmetic_primePower hp, bblrBPrimeFactor_eq_pairSeries hp]
  simp only [add_zero, mul_zero, neg_neg]
  rw [pairShiftedPrimeSeries_ratio hM hα hδ hγ hβ hr]
  have hp0 : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hb0 : (p:ℂ)^β ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hp0)
  have he : (p:ℂ)^(-(β+γ))=(p:ℂ)^(-γ)/(p:ℂ)^β := by
    rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hp0]
    congr 1
    ring
  rw [he, bblrEtaPrimePolynomial_normalized _ _ _ hb0,
    bblrEtaCorrection_eq_crossedPrimeFactor hp]
  ring

theorem bblrPrimePowerNorm_le {p : ℕ} (hp : p.Prime) (z : ℂ) {e : ℝ}
    (hz : z.re ≤ e) : ‖(p:ℂ)^z‖ ≤ (p:ℝ)^e := by
  rw [Complex.norm_natCast_cpow_of_pos hp.pos]
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) hz

theorem bblrEta_eq_B_primePower_of_small_shifts {p : ℕ} (hp : p.Prime)
    (α β γ δ : ℂ) (hα : ‖α‖ ≤ 1/8) (hβ : ‖β‖ ≤ 1/8)
    (hγ : ‖γ‖ ≤ 1/8) (hδ : ‖δ‖ ≤ 1/8) (ν : ℕ) :
    bblrNormalizedEtaArithmetic α β γ δ 0 (p^ν) =
      bblrBPrimeFactor p α (-δ) γ (-β) ν := by
  have hre (z : ℂ) (hz : ‖z‖ ≤ 1/8) : |z.re| ≤ 1/8 :=
    (Complex.abs_re_le_norm _).trans hz
  apply bblrEta_eq_B_primePower hp α β γ δ
    (M := (p:ℝ)^(1/8:ℝ)) (Real.rpow_nonneg (by positivity) _)
  · apply bblrPrimePowerNorm_le hp
    simp only [Complex.neg_re]
    linarith [(abs_le.mp (hre α hα)).1]
  · exact bblrPrimePowerNorm_le hp δ (abs_le.mp (hre δ hδ)).2
  · apply bblrPrimePowerNorm_le hp
    simp only [Complex.neg_re]
    linarith [(abs_le.mp (hre γ hγ)).1]
  · exact bblrPrimePowerNorm_le hp β (abs_le.mp (hre β hβ)).2
  · rw [primePolarGeometricRadius ⟨p,hp⟩ (1/8)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by norm_num)

def bblrBFactor (α β γ δ : ℂ) (a : ℕ) : ℂ :=
  a.factorization.prod fun p ν => bblrBPrimeFactor p α β γ δ ν

theorem bblrEta_eq_B (α β γ δ : ℂ)
    (hα : ‖α‖ ≤ 1/8) (hβ : ‖β‖ ≤ 1/8)
    (hγ : ‖γ‖ ≤ 1/8) (hδ : ‖δ‖ ≤ 1/8) {a : ℕ} (ha : a ≠ 0) :
    (a:ℂ)^β*bblrEtaArithmetic α β γ δ 0 0 (β+δ) a =
      bblrBFactor α (-δ) γ (-β) a := by
  have hn := bblrNormalizedEtaArithmetic_multiplicative α β γ δ 0
  have happ := bblrNormalizedEtaArithmetic_apply α β γ δ 0 ha
  simp only [add_zero, mul_zero] at happ
  rw [← happ, ArithmeticFunction.IsMultiplicative.multiplicative_factorization _ hn ha]
  unfold bblrBFactor Finsupp.prod
  apply Finset.prod_congr rfl
  intro p hp
  exact bblrEta_eq_B_primePower_of_small_shifts (Nat.prime_of_mem_primeFactors hp)
    α β γ δ hα hβ hγ hδ _

theorem bblrNormalizedEtaArithmetic_eq_B (α β γ δ : ℂ)
    (hα : ‖α‖ ≤ 1/8) (hβ : ‖β‖ ≤ 1/8)
    (hγ : ‖γ‖ ≤ 1/8) (hδ : ‖δ‖ ≤ 1/8) {a : ℕ} (ha : a ≠ 0) :
    bblrNormalizedEtaArithmetic α β γ δ 0 a = bblrBFactor α (-δ) γ (-β) a := by
  rw [bblrNormalizedEtaArithmetic_apply _ _ _ _ _ ha]
  simp only [add_zero, mul_zero]
  exact bblrEta_eq_B α β γ δ hα hβ hγ hδ ha

end
end Sechstmoment
