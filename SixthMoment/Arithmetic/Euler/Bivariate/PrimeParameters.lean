import SixthMoment.Arithmetic.Euler.Bivariate.OriginalTailBridge

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace SixthMoment.Source.NoDPLocalClosure
open NoDPLocal NoDPResidues
open scoped BigOperators

noncomputable def primeScale (p : ℕ) (ρ : ℝ) : ℝ := (p:ℝ)^ρ
noncomputable def primeX (p : ℕ) : ℂ := (p:ℂ)⁻¹

theorem primeRoot_ne_zero (p : ℕ) (hp : p ≠ 0) (shift : ℂ) : primeRoot p shift ≠ 0 := by
  intro h
  have H := (Complex.cpow_eq_zero_iff (p:ℂ) (-shift)).mp h
  exact hp (by exact_mod_cast H.1)

theorem primeRoot_norm (p : ℕ) (hp : 0 < p) (shift : ℂ) :
    ‖primeRoot p shift‖ = (p:ℝ)^(-shift.re) := by
  simpa only [primeRoot, Complex.neg_re] using Complex.norm_natCast_cpow_of_pos hp (-shift)

theorem primeRoot_inv_norm (p : ℕ) (hp : 0 < p) (shift : ℂ) :
    ‖(primeRoot p shift)⁻¹‖ = (p:ℝ)^shift.re := by
  simp only [primeRoot, Complex.cpow_neg, inv_inv]
  exact Complex.norm_natCast_cpow_of_pos hp shift

theorem primeRoot_bound (p : ℕ) (hp : p.Prime) (shift : ℂ) (ρ : ℝ) (hshift : ‖shift‖ ≤ ρ) :
    ‖primeRoot p shift‖ ≤ primeScale p ρ := by
  rw [primeRoot_norm p hp.pos shift]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le)
  have H := Complex.abs_re_le_norm shift
  linarith [neg_abs_le shift.re]

theorem primeRoot_inv_bound (p : ℕ) (hp : p.Prime) (shift : ℂ) (ρ : ℝ) (hshift : ‖shift‖ ≤ ρ) :
    ‖(primeRoot p shift)⁻¹‖ ≤ primeScale p ρ := by
  rw [primeRoot_inv_norm p hp.pos shift]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le)
  exact (Complex.re_le_norm shift).trans hshift

theorem primeScale_one_le (p : ℕ) (hp : p.Prime) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    1 ≤ primeScale p ρ := Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) hρ

theorem inverse_rpow_identity (t : ℝ) (ht : 0 < t) (ρ : ℝ) (k l : ℕ) :
    (t⁻¹)^k*(t^ρ)^l = t^(-(k:ℝ)+(l:ℝ)*ρ) := by
  have H1 : (t⁻¹)^k = t^(-(k:ℝ)) := by rw [Real.rpow_neg ht.le, Real.rpow_natCast, inv_pow]
  have H2 : (t^ρ)^l = t^((l:ℝ)*ρ) := by
    rw [mul_comm (l:ℝ) ρ, Real.rpow_mul ht.le, Real.rpow_natCast]
  rw [H1, H2, ← Real.rpow_add ht]

theorem prime_weight_identity (p : ℕ) (hp : p.Prime) (ρ : ℝ) (k l : ℕ) :
    ‖primeX p‖^k*(primeScale p ρ)^l = (p:ℝ)^(-(k:ℝ)+(l:ℝ)*ρ) := by
  simp only [primeX, norm_inv, Complex.norm_natCast, primeScale]
  exact inverse_rpow_identity (p:ℝ) (by exact_mod_cast hp.pos) ρ k l

theorem prime_uniform_region (p : ℕ) (hp : p.Prime) (ρ : ℝ) (hρ : ρ < 1/4) :
    ‖primeX p‖*(primeScale p ρ)^4 < 1 := by
  have H := prime_weight_identity p hp ρ 1 4
  simp only [pow_one, Nat.cast_one, Nat.cast_ofNat] at H
  rw [H]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt)
  linarith

theorem prime_pole_parameter (p : ℕ) (hp : p.Prime) (shift : ℂ) :
    (p:ℂ)^(-(1-shift)) = primeX p/primeRoot p shift := by
  have hp' : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [show -(1-shift) = (-1:ℂ)+shift by ring, Complex.cpow_add _ _ hp', Complex.cpow_neg_one]
  simp only [primeX, primeRoot, Complex.cpow_neg, div_eq_mul_inv, inv_inv]

theorem prime_boundary_parameter (p : ℕ) (hp : p.Prime) :
    primeX p/(1-primeX p) = 1/((p:ℂ)-1) := by
  have hp' : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1' : (p:ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hp.one_lt)
  have hp1 : (p:ℂ)-1 ≠ 0 := sub_ne_zero.mpr hp1'
  unfold primeX
  field_simp [hp', hp1]

end SixthMoment.Source.NoDPLocalClosure
