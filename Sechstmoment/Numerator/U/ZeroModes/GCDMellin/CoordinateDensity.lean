import Sechstmoment.Numerator.U.ZeroModes.Ratio.GCDVStarCoordinates

/-! Exact positive-real power density in the BBLR GCD coordinate.
The factor d precedes the true h-Mellin weight d^(-s), producing d^(1-s). -/
namespace Sechstmoment
open Complex Real Source
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

private theorem gcdPositiveCpow (r : ℝ) (hr : 0<r) (z : ℂ) :
    (r:ℂ)^z=Complex.exp ((Real.log r:ℂ)*z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),←Complex.ofReal_log hr.le]

theorem a03GCDCoordinateQuad_denominator_inv (α : MomentShifts)
    {a b m n X : ℝ} (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) (hX : 0<X) :
    (a03ZeroModeRealQuadDenominator α 0 ![m,X/(a*m),n,X/(b*n)])⁻¹=
      (a:ℂ)^(1/2+α 1)*(b:ℂ)^(1/2+α 3)*(m:ℂ)^(-α 0+α 1)*
        (n:ℂ)^(-α 2+α 3)*(X:ℂ)^(-1-α 1-α 3) := by
  have hlM : Real.log (X/(a*m))=Real.log X-Real.log a-Real.log m := by
    rw [Real.log_div hX.ne' (mul_pos ha hm).ne',Real.log_mul ha.ne' hm.ne']
    ring
  have hlN : Real.log (X/(b*n))=Real.log X-Real.log b-Real.log n := by
    rw [Real.log_div hX.ne' (mul_pos hb hn).ne',Real.log_mul hb.ne' hn.ne']
    ring
  simp only [a03ZeroModeRealQuadDenominator,Fin.prod_univ_four,add_zero]
  norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons]
  simp_rw [gcdPositiveCpow m hm,gcdPositiveCpow (X/(a*m)) (div_pos hX (mul_pos ha hm)),
    gcdPositiveCpow n hn,gcdPositiveCpow (X/(b*n)) (div_pos hX (mul_pos hb hn)),
    gcdPositiveCpow a ha,gcdPositiveCpow b hb,gcdPositiveCpow X hX,hlM,hlN]
  simp only [Complex.ofReal_sub,←Complex.exp_add,←Complex.exp_neg]
  congr 1
  ring

/-- The actual two reciprocal-square-root amplifier powers and the real
Jacobian combine with the shifted native quad denominator exactly. -/
theorem a03GCDCoordinate_full_density (α : MomentShifts)
    {a b m n X : ℝ} (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) (hX : 0<X) (d : ℝ) :
    ((d/(a*b*m*n):ℝ):ℂ)*(a:ℂ)^(-(1/2:ℂ))*(b:ℂ)^(-(1/2:ℂ))*
      (a03ZeroModeRealQuadDenominator α 0 ![m,X/(a*m),n,X/(b*n)])⁻¹=
      (d:ℂ)*(a:ℂ)^(-1+α 1)*(b:ℂ)^(-1+α 3)*
        (m:ℂ)^(-1-α 0+α 1)*(n:ℂ)^(-1-α 2+α 3)*(X:ℂ)^(-1-α 1-α 3) := by
  have hbase : ((d/(a*b*m*n):ℝ):ℂ)=
      (d:ℂ)*(a:ℂ)^(-1:ℂ)*(b:ℂ)^(-1:ℂ)*(m:ℂ)^(-1:ℂ)*(n:ℂ)^(-1:ℂ) := by
    simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.cpow_neg_one]
    ring
  rw [a03GCDCoordinateQuad_denominator_inv α ha hb hm hn hX]
  calc
    _=(d:ℂ)*((a:ℂ)^(-1:ℂ)*(b:ℂ)^(-1:ℂ)*(m:ℂ)^(-1:ℂ)*(n:ℂ)^(-1:ℂ)*
        (a:ℂ)^(-(1/2:ℂ))*(b:ℂ)^(-(1/2:ℂ))*
        ((a:ℂ)^(1/2+α 1)*(b:ℂ)^(1/2+α 3)*(m:ℂ)^(-α 0+α 1)*
          (n:ℂ)^(-α 2+α 3)*(X:ℂ)^(-1-α 1-α 3))) := by rw [hbase]; ring
    _=(d:ℂ)*((a:ℂ)^(-1+α 1)*(b:ℂ)^(-1+α 3)*
        (m:ℂ)^(-1-α 0+α 1)*(n:ℂ)^(-1-α 2+α 3)*(X:ℂ)^(-1-α 1-α 3)) := by
      congr 1
      simp_rw [gcdPositiveCpow a ha,gcdPositiveCpow b hb,gcdPositiveCpow m hm,
        gcdPositiveCpow n hn,gcdPositiveCpow X hX]
      simp only [←Complex.exp_add]
      congr 1
      ring
    _=_ := by ring

theorem a03_native_GCD_amplifier_density (T A B : ℝ) (f g : ℝ→ℝ) (α : MomentShifts)
    (w : Fin 5→ℕ) (hw : ∀ j,1≤w j) {X : ℝ} (hX : 0<X) :
    phaseActualAmplifierCoefficient T f A (w 0)*phaseActualAmplifierCoefficient T g B (w 1)*
      (a03NativeGCDCoordinateScale w:ℂ)*
        (a03ZeroModeRealQuadDenominator α 0 (a03NativeGCDCoordinateQuad w X))⁻¹=
      ((rectangularSmoothBlockWeight ((w 0:ℝ)/A):ℂ)*(f (Real.log (w 0:ℝ)/Real.log T):ℂ)*
        (rectangularSmoothBlockWeight ((w 1:ℝ)/B):ℂ)*(g (Real.log (w 1:ℝ)/Real.log T):ℂ))*
      (Nat.gcd (w 0*w 2) (w 1*w 3):ℂ)*(w 0:ℂ)^(-1+α 1)*(w 1:ℂ)^(-1+α 3)*
        (w 2:ℂ)^(-1-α 0+α 1)*(w 3:ℂ)^(-1-α 2+α 3)*(X:ℂ)^(-1-α 1-α 3) := by
  have hp (j : Fin 5) : (0:ℝ)<w j := by exact_mod_cast (show 0<w j by have := hw j; omega)
  have he := a03GCDCoordinate_full_density α (hp 0) (hp 1) (hp 2) (hp 3) hX
    (Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)
  simp only [a03NativeGCDCoordinateQuad,a03NativeGCDCoordinateScale,phaseActualAmplifierCoefficient]
  have hc (r : ℕ) : ((r:ℝ):ℂ)=(r:ℂ) := by simp
  simp only [hc] at he
  calc
    _=((rectangularSmoothBlockWeight ((w 0:ℝ)/A):ℂ)*(f (Real.log (w 0:ℝ)/Real.log T):ℂ)*
        (rectangularSmoothBlockWeight ((w 1:ℝ)/B):ℂ)*(g (Real.log (w 1:ℝ)/Real.log T):ℂ))*
      ((((Nat.gcd (w 0*w 2) (w 1*w 3):ℝ)/((w 0:ℝ)*w 1*w 2*w 3):ℝ):ℂ)*
        (w 0:ℂ)^(-(1/2:ℂ))*(w 1:ℂ)^(-(1/2:ℂ))*
          (a03ZeroModeRealQuadDenominator α 0 ![(w 2:ℝ),X/((w 0:ℝ)*w 2),(w 3:ℝ),X/((w 1:ℝ)*w 3)])⁻¹) := by ring
    _=_ := by rw [he]; ring

end
end Sechstmoment
