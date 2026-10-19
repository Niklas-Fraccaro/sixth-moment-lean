import Sechstmoment.Analysis.Integration.ExponentialDifference
import Sechstmoment.Arithmetic.QuadraticDivisor.Definitions
import Sechstmoment.Numerator.Kernels.Nodes
import Sechstmoment.Numerator.Polar.General.Source
import Sechstmoment.Zeta.Moments.SixTerms

/-! Exact algebraic identification of the six BBLR convolution pole terms
with the four-by-four exponential alternant. The first profile mass pairs
with the lower source shifts and the second with the upper source shifts.
No DP four-residue generator or analytical asymptotic input is used. -/

namespace Sechstmoment
open Complex Source
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

/-- One of the six literal inverse polar factors, before integration over
the common positive convolution variable. -/
def bblrExponentialConvolutionPoleTerm (σ : MomentShifts) (A B t : ℝ)
    (m : Fin 6) : ℂ :=
  Complex.exp (bblrSixPhaseExponents σ m)*
    exponentialDifference (bblrSixShifts σ m 2) (bblrSixShifts σ m 3) (A-t)*
    exponentialDifference (bblrSixShifts σ m 0) (bblrSixShifts σ m 1) (B-t)/
      ((bblrSixShifts σ m 0 + bblrSixShifts σ m 2)*
        (bblrSixShifts σ m 0 + bblrSixShifts σ m 3)*
        (bblrSixShifts σ m 1 + bblrSixShifts σ m 2)*
        (bblrSixShifts σ m 1 + bblrSixShifts σ m 3))

private def bblrConvolutionAlternantMinor (M : Matrix (Fin 4) (Fin 4) ℂ)
    (m : Fin 6) : ℂ :=
  ![matrixMinorTwo M 0 1 0 1*matrixMinorTwo M 2 3 2 3,
    matrixMinorTwo M 2 3 0 1*matrixMinorTwo M 0 1 2 3,
    matrixMinorTwo M 1 2 0 1*matrixMinorTwo M 0 3 2 3,
    -(matrixMinorTwo M 1 3 0 1*matrixMinorTwo M 0 2 2 3),
    -(matrixMinorTwo M 0 2 0 1*matrixMinorTwo M 1 3 2 3),
    matrixMinorTwo M 0 3 0 1*matrixMinorTwo M 1 2 2 3] m

private theorem expAlternantMinor_first (x : Fin 4 → ℂ) (u v : ℝ) (i j : Fin 4) :
    matrixMinorTwo (expAlternantMatrix x (numeratorRho u v)) i j 0 1 =
      Complex.exp (-x i-x j) * (Complex.exp (x j*(v:ℂ))-Complex.exp (x i*(v:ℂ))) := by
  change Complex.exp (x i * (-1)) * Complex.exp (x j*((v:ℂ)-1)) -
    Complex.exp (x i*((v:ℂ)-1)) * Complex.exp (x j*(-1)) = _
  simp only [mul_sub]
  congr 1
  · rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  · rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring

private theorem expAlternantMinor_second (x : Fin 4 → ℂ) (u v : ℝ) (i j : Fin 4) :
    matrixMinorTwo (expAlternantMatrix x (numeratorRho u v)) i j 2 3 =
      Complex.exp (-x i*(u:ℂ))-Complex.exp (-x j*(u:ℂ)) := by
  change Complex.exp (x i*(-(u:ℂ))) * Complex.exp (x j*0) -
    Complex.exp (x i*0) * Complex.exp (x j*(-(u:ℂ))) = _
  simp only [mul_zero, Complex.exp_zero, mul_one, one_mul]
  congr 1 <;> congr 1 <;> ring

private theorem bblrExponentialConvolutionPoleTerm_eq_minor
    (σ : MomentShifts) (hσ : Function.Injective (polarSourceKnots σ))
    (A B t : ℝ) (m : Fin 6) :
    bblrExponentialConvolutionPoleTerm σ A B t m =
      Complex.exp (polarSourceKnots σ 0+polarSourceKnots σ 1)*
        bblrConvolutionAlternantMinor
          (expAlternantMatrix (polarSourceKnots σ) (numeratorRho (A-t) (B-t))) m /
          fourVandermonde (polarSourceKnots σ) := by
  have h01 : σ 1-σ 0 ≠ 0 := by
    intro hz
    apply hσ.ne (show (0:Fin 4) ≠ 1 by decide)
    change -σ 0 = -σ 1
    linear_combination hz
  have h23 : σ 3-σ 2 ≠ 0 := by
    intro hz
    apply hσ.ne (show (2:Fin 4) ≠ 3 by decide)
    change σ 2 = σ 3
    linear_combination -hz
  have h02 : σ 0+σ 2 ≠ 0 := by
    intro hz
    apply hσ.ne (show (0:Fin 4) ≠ 2 by decide)
    change -σ 0 = σ 2
    linear_combination -hz
  have h03 : σ 0+σ 3 ≠ 0 := by
    intro hz
    apply hσ.ne (show (0:Fin 4) ≠ 3 by decide)
    change -σ 0 = σ 3
    linear_combination -hz
  have h12 : σ 1+σ 2 ≠ 0 := by
    intro hz
    apply hσ.ne (show (1:Fin 4) ≠ 2 by decide)
    change -σ 1 = σ 2
    linear_combination -hz
  have h13 : σ 1+σ 3 ≠ 0 := by
    intro hz
    apply hσ.ne (show (1:Fin 4) ≠ 3 by decide)
    change -σ 1 = σ 3
    linear_combination -hz
  have hn01 : -σ 1 + σ 0 ≠ 0 := by
    intro h
    apply h01
    linear_combination -h
  have hn23 : -σ 3 + σ 2 ≠ 0 := by
    intro h
    apply h23
    linear_combination -h
  have hn02 : -σ 2 + -σ 0 ≠ 0 := by
    intro h
    apply h02
    linear_combination -h
  have hn12 : -σ 2 + -σ 1 ≠ 0 := by
    intro h
    apply h12
    linear_combination -h
  have hn03 : -σ 3 + -σ 0 ≠ 0 := by
    intro h
    apply h03
    linear_combination -h
  have hn13 : -σ 3 + -σ 1 ≠ 0 := by
    intro h
    apply h13
    linear_combination -h
  have hp03 : σ 3 + σ 0 ≠ 0 := by
    intro h
    apply h03
    linear_combination h
  have hp13 : σ 3 + σ 1 ≠ 0 := by
    intro h
    apply h13
    linear_combination h
  have h02b : -σ 0 - σ 2 ≠ 0 := by
    intro h
    apply h02
    linear_combination -h
  have h02c : -σ 2 - σ 0 ≠ 0 := by
    intro h
    apply h02
    linear_combination -h
  have h01a : σ 1 + -σ 0 ≠ 0 := by
    intro h
    apply h01
    linear_combination h
  have h01b : σ 0 + -σ 1 ≠ 0 := by
    intro h
    apply h01
    linear_combination -h
  have h23a : -σ 2 + σ 3 ≠ 0 := by
    intro h
    apply h23
    linear_combination h
  have h12b : -σ 1 - σ 2 ≠ 0 := by
    intro h
    apply h12
    linear_combination -h
  have h03b : -σ 3 - σ 0 ≠ 0 := by
    intro h
    apply h03
    linear_combination -h
  have hV : fourVandermonde (polarSourceKnots σ) ≠ 0 := by
    simp only [fourVandermonde, mul_ne_zero_iff, sub_ne_zero]
    repeat' constructor
    all_goals exact hσ.ne (by decide)
  simp only [polarSourceKnots] at hV
  have he0 : Complex.exp (polarSourceKnots σ 0+polarSourceKnots σ 1)*
      Complex.exp (-polarSourceKnots σ 0-polarSourceKnots σ 1) =
      Complex.exp (bblrSixPhaseExponents σ 0) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num [polarSourceKnots, bblrSixPhaseExponents]
    ring
  have he1 : Complex.exp (polarSourceKnots σ 0+polarSourceKnots σ 1)*
      Complex.exp (-polarSourceKnots σ 2-polarSourceKnots σ 3) =
      Complex.exp (bblrSixPhaseExponents σ 1) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num [polarSourceKnots, bblrSixPhaseExponents]
    ring
  have he2 : Complex.exp (polarSourceKnots σ 0+polarSourceKnots σ 1)*
      Complex.exp (-polarSourceKnots σ 1-polarSourceKnots σ 2) =
      Complex.exp (bblrSixPhaseExponents σ 2) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num [polarSourceKnots, bblrSixPhaseExponents]
    ring
  have he3 : Complex.exp (polarSourceKnots σ 0+polarSourceKnots σ 1)*
      Complex.exp (-polarSourceKnots σ 1-polarSourceKnots σ 3) =
      Complex.exp (bblrSixPhaseExponents σ 3) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num [polarSourceKnots, bblrSixPhaseExponents]
    ring
  have he4 : Complex.exp (polarSourceKnots σ 0+polarSourceKnots σ 1)*
      Complex.exp (-polarSourceKnots σ 0-polarSourceKnots σ 2) =
      Complex.exp (bblrSixPhaseExponents σ 4) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num [polarSourceKnots, bblrSixPhaseExponents]
    ring
  have he5 : Complex.exp (polarSourceKnots σ 0+polarSourceKnots σ 1)*
      Complex.exp (-polarSourceKnots σ 0-polarSourceKnots σ 3) =
      Complex.exp (bblrSixPhaseExponents σ 5) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num [polarSourceKnots, bblrSixPhaseExponents]
    ring
  fin_cases m <;>
    norm_num [bblrConvolutionAlternantMinor, expAlternantMinor_first, expAlternantMinor_second]
  all_goals
    simp only [← mul_assoc, he0, he1, he2, he3, he4, he5]
    norm_num [bblrExponentialConvolutionPoleTerm, exponentialDifference,
      bblrSixShifts, bblrSixPhaseExponents, polarSourceKnots]
    field_simp [hV,h01,h23,h02,h03,h12,h13, hn01, hn23, hn02, hn12, hn03, hn13, hp03, hp13, h02b, h02c, h01a, h01b, h23a, h12b, h03b]
    norm_num [fourVandermonde, polarSourceKnots]
    ring

/-- The six signed BBLR convolution terms are exactly the genuine
exponential determinant, with its original Vandermonde convention. -/
theorem bblrSixExponentialConvolution_eq_alternant
    (σ : MomentShifts) (hσ : Function.Injective (polarSourceKnots σ))
    (A B t : ℝ) :
    (∑ m : Fin 6, bblrExponentialConvolutionPoleTerm σ A B t m) =
      exponentialAlternant (polarSourceKnots σ) (numeratorRho (A-t) (B-t)) := by
  simp_rw [bblrExponentialConvolutionPoleTerm_eq_minor σ hσ A B t]
  rw [exponentialAlternant_six_minors]
  norm_num [bblrConvolutionAlternantMinor, Fin.sum_univ_succ]
  ring

end
end Sechstmoment
