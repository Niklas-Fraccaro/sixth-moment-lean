import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Sechstmoment.Zeta.FunctionalEquation

/-!
# Actual zeta generators and their centered derivatives

The finite binomial formula is connected to derivatives of the actual Riemann
zeta generator. Only the pole at `s = 1` is excluded. No moment asymptotic is
asserted in this module.
-/

namespace Sechstmoment

open Complex

noncomputable section

/-- The normalized shifted generator `exp(z/2) ζ(s + z/log T)`. -/
def shiftedZetaGenerator (T : ℝ) (s z : ℂ) : ℂ :=
  Complex.exp (z / 2) * riemannZeta (s + z / (Real.log T : ℂ))

/-- The explicit finite expansion of `(1/2 + (log T)⁻¹ ∂s)^m ζ(s)`. -/
def centeredZetaDerivative (T : ℝ) (m : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1),
    (m.choose j : ℂ) * (1 / 2 : ℂ) ^ (m - j) / (Real.log T : ℂ) ^ j *
      iteratedDeriv j riemannZeta s

/-- Nonzero affine rescaling commutes with all iterated derivatives. -/
theorem iteratedDeriv_comp_nonzero_const_mul (n : ℕ) (f : ℂ → ℂ)
    (c : ℂ) (hc : c ≠ 0) (x : ℂ) :
    iteratedDeriv n (fun z => f (c * z)) x = c ^ n * iteratedDeriv n f (c * x) := by
  let e : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)
  have he : ∀ z : ℂ, e z = c * z := by
    intro z
    simp [e, smul_eq_mul]
  have h := e.iteratedFDerivWithin_comp_right f
    (s := Set.univ) uniqueDiffOn_univ (x := x) (Set.mem_univ _) n
  simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at h
  rw [iteratedDeriv_eq_iteratedFDeriv]
  change (iteratedFDeriv ℂ n (f ∘ e) x) (fun _ => 1) = _
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [ContinuousLinearEquiv.coe_coe, he, mul_one]
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
  simp [Finset.prod_const, smul_eq_mul]

/-- Derivatives of the shifted zeta argument, including all orders. -/
theorem iteratedDeriv_shifted_riemannZeta (T : ℝ) (s : ℂ) (n : ℕ)
    (hT : Real.log T ≠ 0) :
    iteratedDeriv n (fun z : ℂ => riemannZeta (s + z / (Real.log T : ℂ))) 0 =
      iteratedDeriv n riemannZeta s / (Real.log T : ℂ) ^ n := by
  have hc : (Real.log T : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Complex.ofReal_ne_zero.mpr hT)
  have h := iteratedDeriv_comp_nonzero_const_mul n
    (fun z : ℂ => riemannZeta (s + z)) (Real.log T : ℂ)⁻¹ hc 0
  simpa [div_eq_mul_inv, mul_comm, iteratedDeriv_comp_const_add] using h

/-- The actual generator realizes the finite centered-derivative expansion. -/
theorem iteratedDeriv_shiftedZetaGenerator (T : ℝ) (s : ℂ) (m : ℕ)
    (hT : Real.log T ≠ 0) (hs : s ≠ 1) :
    iteratedDeriv m (shiftedZetaGenerator T s) 0 = centeredZetaDerivative T m s := by
  have hz : ContDiffAt ℂ m riemannZeta s :=
    (analyticOn_riemannZeta s (by simpa using hs)).contDiffAt
  have hshift : ContDiffAt ℂ m
      (fun z : ℂ => riemannZeta (s + z / (Real.log T : ℂ))) 0 := by
    have hz' : ContDiffAt ℂ m riemannZeta (s + (0 : ℂ) / (Real.log T : ℂ)) := by
      simpa using hz
    exact hz'.comp 0 (by fun_prop)
  have hexp : ContDiffAt ℂ m (fun z : ℂ => Complex.exp ((1 / 2 : ℂ) * z)) 0 := by
    fun_prop
  have hgen : shiftedZetaGenerator T s = fun z : ℂ =>
      riemannZeta (s + z / (Real.log T : ℂ)) * Complex.exp ((1 / 2 : ℂ) * z) := by
    funext z
    simp only [shiftedZetaGenerator]
    rw [mul_comm]
    congr 2
    ring
  rw [hgen, iteratedDeriv_fun_mul hshift hexp]
  unfold centeredZetaDerivative
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDeriv_shifted_riemannZeta T s j hT, iteratedDeriv_cexp_const_mul]
  simp only [mul_zero, Complex.exp_zero, mul_one]
  ring

@[simp] theorem shiftedZetaGenerator_zero (T : ℝ) (s : ℂ) :
    shiftedZetaGenerator T s 0 = riemannZeta s := by
  simp [shiftedZetaGenerator]

@[simp] theorem centeredZetaDerivative_zero (T : ℝ) (s : ℂ) :
    centeredZetaDerivative T 0 s = riemannZeta s := by
  simp [centeredZetaDerivative]

theorem centeredZetaDerivative_one (T : ℝ) (s : ℂ) :
    centeredZetaDerivative T 1 s =
      (1 / 2 : ℂ) * riemannZeta s + deriv riemannZeta s / (Real.log T : ℂ) := by
  simp [centeredZetaDerivative, Finset.sum_range_succ, iteratedDeriv_one, div_eq_mul_inv,
    mul_comm]

theorem centeredZetaDerivative_two (T : ℝ) (s : ℂ) :
    centeredZetaDerivative T 2 s =
      (1 / 4 : ℂ) * riemannZeta s + deriv riemannZeta s / (Real.log T : ℂ) +
        iteratedDeriv 2 riemannZeta s / (Real.log T : ℂ) ^ 2 := by
  simp only [centeredZetaDerivative, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, Nat.cast_one,
    Nat.cast_ofNat, Nat.sub_zero, Nat.sub_self, pow_zero, div_one, pow_one, one_mul,
    iteratedDeriv_zero, iteratedDeriv_one, zero_add]
  norm_num
  ring

/-- Logarithmic normalization is nonzero throughout the intended range `T > 1`. -/
theorem log_ne_zero_of_one_lt {T : ℝ} (hT : 1 < T) : Real.log T ≠ 0 :=
  (Real.log_pos hT).ne'

/-- The derivative bridge in the intended asymptotic parameter range. -/
theorem iteratedDeriv_shiftedZetaGenerator_of_one_lt (T : ℝ) (s : ℂ) (m : ℕ)
    (hT : 1 < T) (hs : s ≠ 1) :
    iteratedDeriv m (shiftedZetaGenerator T s) 0 = centeredZetaDerivative T m s :=
  iteratedDeriv_shiftedZetaGenerator T s m (log_ne_zero_of_one_lt hT) hs

/-- All orders of the centered bridge are valid on the whole critical line. -/
theorem iteratedDeriv_shiftedZetaGenerator_criticalLine (T t : ℝ) (m : ℕ)
    (hT : 1 < T) :
    iteratedDeriv m (shiftedZetaGenerator T (criticalLinePoint t)) 0 =
      centeredZetaDerivative T m (criticalLinePoint t) :=
  iteratedDeriv_shiftedZetaGenerator_of_one_lt T (criticalLinePoint t) m hT
    (criticalLinePoint_ne_one t)

end
end Sechstmoment
