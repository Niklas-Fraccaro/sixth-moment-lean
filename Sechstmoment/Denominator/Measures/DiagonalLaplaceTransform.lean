import Sechstmoment.Denominator.Measures.DiagonalMeasureDefinitions
import Sechstmoment.Denominator.Measures.EulerLaplace

/-! The Laplace transform of the actual logarithmic atomic diagonal measure,
with integrability and the arithmetic transform limit proved. -/

namespace Sechstmoment
open Complex Real Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

private theorem d01LeftTriple_exponential (L : ℝ) (a : Fin 3 → ℂ)
    (x : DiagonalSixIndices) :
    literalTripleDirichletTerm (fun i => a i/(L : ℂ)) x.val.1 =
      Complex.exp (-(∑ i, a i * ((d01LogPoint L x).1 i : ℂ))) := by
  have hp : literalTripleDirichletTerm (fun i => a i/(L : ℂ)) x.val.1 =
      ∏ i : Fin 3, shiftedPowerArithmetic (a i/(L : ℂ)) (d01LeftIndices x i) := by
    simp [literalTripleDirichletTerm, d01LeftIndices, Fin.prod_univ_succ]
    ring
  rw [hp]
  simp_rw [d01ScaledPowerArithmetic_eq_exp L _ (Nat.ne_of_gt (d01LeftIndices_pos x _))]
  rw [← Complex.exp_sum]
  congr 1
  simp only [d01LogPoint, neg_mul, Finset.sum_neg_distrib]

private theorem d01RightTriple_exponential (L : ℝ) (b : Fin 3 → ℂ)
    (x : DiagonalSixIndices) :
    literalTripleDirichletTerm (fun i => b i/(L : ℂ)) x.val.2 =
      Complex.exp (-(∑ i, b i * ((d01LogPoint L x).2 i : ℂ))) := by
  have hp : literalTripleDirichletTerm (fun i => b i/(L : ℂ)) x.val.2 =
      ∏ i : Fin 3, shiftedPowerArithmetic (b i/(L : ℂ)) (d01RightIndices x i) := by
    simp [literalTripleDirichletTerm, d01RightIndices, Fin.prod_univ_succ]
    ring
  rw [hp]
  simp_rw [d01ScaledPowerArithmetic_eq_exp L _ (Nat.ne_of_gt (d01RightIndices_pos x _))]
  rw [← Complex.exp_sum]
  congr 1
  simp only [d01LogPoint, neg_mul, Finset.sum_neg_distrib]

theorem d01Atomic_complexLaplace_identity (L : ℝ) (a b : Fin 3 → ℂ)
    (x : DiagonalSixIndices) :
    (d01AtomicWeight L x : ℂ) * d01ComplexLaplaceWeight (a,b) (d01LogPoint L x) =
      literalDiagonalSixTerm (fun i => a i/(L : ℂ))
        (fun i => b i/(L : ℂ)) x / (L : ℂ)^9 := by
  unfold literalDiagonalSixTerm
  rw [d01LeftTriple_exponential, d01RightTriple_exponential,
    shiftedPowerArithmetic_apply 1 x.property.2, Complex.cpow_neg_one,
    ← Complex.exp_add, ← neg_add]
  unfold d01AtomicWeight d01ComplexLaplaceWeight d01CommonProduct
  simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_inv,
    Complex.ofReal_natCast]
  ring

theorem d01ComplexLaplaceWeight_integrable {L : ℝ} (hL : 0 < L)
    (a b : Fin 3 → ℂ) (ha : ∀ i, 0 < (a i).re) (hb : ∀ i, 0 < (b i).re) :
    Integrable (d01ComplexLaplaceWeight (a,b)) (d01DiagonalMeasure L) := by
  rw [d01DiagonalMeasure_integrable_iff hL.le]
  have hs := d01ScaledDiagonalSixTerm_norm_summable hL a b ha hb
  apply (hs.div_const ‖(L : ℂ)^9‖).congr
  intro x
  have hi := congrArg norm (d01Atomic_complexLaplace_identity L a b x)
  simpa only [norm_mul, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (d01AtomicWeight_nonneg hL.le x)] using hi.symm

theorem d01DiagonalMeasure_complexLaplace_eq {L : ℝ} (hL : 0 ≤ L)
    (a b : Fin 3 → ℂ) :
    (∫ y, d01ComplexLaplaceWeight (a,b) y ∂d01DiagonalMeasure L) =
      d01NormalizedDiagonalLaplace L a b := by
  rw [d01DiagonalMeasure_integral hL]
  simp only [Complex.real_smul, d01Atomic_complexLaplace_identity]
  rw [tsum_div_const]
  rfl

theorem d01DiagonalMeasure_complexLaplace_tendsto (a b : Fin 3 → ℂ)
    (ha : ∀ i, 0 < (a i).re) (hb : ∀ i, 0 < (b i).re) :
    Tendsto (fun L : ℝ => ∫ y, d01ComplexLaplaceWeight (a,b) y ∂d01DiagonalMeasure L)
      atTop (𝓝 ((arithmeticFactor : ℂ) * ∏ ij : Fin 3 × Fin 3, 1/(a ij.1+b ij.2))) := by
  apply (d01NormalizedDiagonalLaplace_tendsto a b ha hb).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact (d01DiagonalMeasure_complexLaplace_eq hL.le a b).symm

theorem d01ComplexLaplaceWeight_ofReal (ab y : D01LogSpace) :
    d01ComplexLaplaceWeight (fun i => (ab.1 i : ℂ), fun j => (ab.2 j : ℂ)) y =
      (d01LaplaceWeight ab y : ℂ) := by
  unfold d01ComplexLaplaceWeight d01LaplaceWeight
  rw [Complex.ofReal_exp]
  congr 1
  simp only [Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_sum,
    Complex.ofReal_mul]

theorem d01ComplexLaplaceWeight_norm (ab : PolarShiftSpace) (y : D01LogSpace) :
    ‖d01ComplexLaplaceWeight ab y‖ =
      d01LaplaceWeight (fun i => (ab.1 i).re, fun j => (ab.2 j).re) y := by
  unfold d01ComplexLaplaceWeight d01LaplaceWeight
  rw [Complex.norm_exp]
  congr 1
  simp only [Complex.neg_re, Complex.add_re, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem d01LaplaceWeight_integrable {L : ℝ} (hL : 0 < L) (ab : D01LogSpace)
    (ha : ∀ i, 0 < ab.1 i) (hb : ∀ i, 0 < ab.2 i) :
    Integrable (d01LaplaceWeight ab) (d01DiagonalMeasure L) := by
  have hc := d01ComplexLaplaceWeight_integrable hL
    (fun i => (ab.1 i : ℂ)) (fun j => (ab.2 j : ℂ)) ha hb
  have hc' : Integrable (fun y => (d01ComplexLaplaceWeight
      (fun i => (ab.1 i : ℂ), fun j => (ab.2 j : ℂ)) y).re)
        (d01DiagonalMeasure L) := hc.re
  simpa only [d01ComplexLaplaceWeight_ofReal, Complex.ofReal_re] using hc'

theorem d01DiagonalMeasure_laplace_tendsto (ab : D01LogSpace)
    (ha : ∀ i, 0 < ab.1 i) (hb : ∀ i, 0 < ab.2 i) :
    Tendsto (fun L : ℝ => ∫ y, d01LaplaceWeight ab y ∂d01DiagonalMeasure L) atTop
      (𝓝 (arithmeticFactor * ∏ ij : Fin 3 × Fin 3, 1/(ab.1 ij.1+ab.2 ij.2))) := by
  have hc := d01DiagonalMeasure_complexLaplace_tendsto
    (fun i => (ab.1 i : ℂ)) (fun j => (ab.2 j : ℂ)) ha hb
  have hcast : ((arithmeticFactor * ∏ ij : Fin 3 × Fin 3,
      1/(ab.1 ij.1+ab.2 ij.2) : ℝ) : ℂ) =
        (arithmeticFactor : ℂ) * ∏ ij : Fin 3 × Fin 3,
          1/((ab.1 ij.1 : ℂ)+(ab.2 ij.2 : ℂ)) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_prod, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_add]
  rw [← hcast] at hc
  simpa only [d01ComplexLaplaceWeight_ofReal, integral_complex_ofReal, Function.comp_def,
    Complex.ofReal_re]
    using Complex.continuous_re.continuousAt.tendsto.comp hc

end
end Sechstmoment
