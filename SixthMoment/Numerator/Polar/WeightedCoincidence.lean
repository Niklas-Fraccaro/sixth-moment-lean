import SixthMoment.Numerator.Polar.General.DP


namespace SixthMoment
open Complex Metric MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

noncomputable def polarPolynomialB (η : ℝ) (P : Polynomial ℝ) (z : ℂ) : ℂ :=
  ∫ a in (0:ℝ)..η, ((Polynomial.eval (1-a/η:ℝ) P:ℝ):ℂ)*polarB a z

noncomputable def polarPolynomialC (η : ℝ) (P : Polynomial ℝ) (z : ℂ) : ℂ :=
  ∫ a in (0:ℝ)..η, ((Polynomial.eval (1-a/η:ℝ) P:ℝ):ℂ)*polarC a z

noncomputable def polarPolynomialJ (η : ℝ) (P : Polynomial ℝ) (z : ℂ) : ℂ :=
  (polarPolynomialB η P z)^2*polarH 2 z +
    (2*polarPolynomialB η P z*polarPolynomialC η P z)*polarH 1 z +
    (polarPolynomialC η P z)^2*polarH 0 z

theorem polarGeneralInverseContour_coincident (x : ℝ) (ω z : ℂ) (R : ℝ)
    (hR : ‖z‖ < R) :
    polarGeneralInverseContour x ω ![0,0,-z,0] R = polarInverseFactor x ω z := by
  have hp (u : ℂ) : (∏ j : Fin 4, (u- (![0,0,-z,0] : Fin 4 → ℂ) j)) =
      u^3*(u+z) := by
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero,Matrix.cons_val_succ]
    ring
  unfold polarGeneralInverseContour
  simp_rw [hp]
  exact polarInverseLaplaceContour_eq_all x ω z R hR

theorem polarGeneralProfile_coincident (η : ℝ) (P : Polynomial ℝ) (ω z : ℂ) (R : ℝ)
    (hR : ‖z‖ < R) :
    polarGeneralProfile η P ![0,0,-z,0] R ω =
      polarPolynomialB η P z+ω*polarPolynomialC η P z := by
  have hB : Continuous (fun a : ℝ =>
      ((Polynomial.eval (1-a/η:ℝ) P:ℝ):ℂ)*polarB a z) := by
    unfold polarB
    fun_prop
  have hC : Continuous (fun a : ℝ =>
      ((Polynomial.eval (1-a/η:ℝ) P:ℝ):ℂ)*polarC a z) := by
    unfold polarC
    fun_prop
  unfold polarGeneralProfile
  simp_rw [polarGeneralInverseContour_coincident _ ω z R hR,polarInverseFactor,
    mul_add,show ∀ a : ℝ, ((Polynomial.eval (1-a/η:ℝ) P:ℝ):ℂ)*(ω*polarC a z) =
      ω*(((Polynomial.eval (1-a/η:ℝ) P:ℝ):ℂ)*polarC a z) by intro a; ring]
  rw [intervalIntegral.integral_add (hB.intervalIntegrable _ _)
    ((hC.const_mul ω).intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  rfl

theorem polar_quadratic_contour_all (A B C z : ℂ) (R : ℝ) (hR : ‖z‖ < R) :
    (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
      (∮ ω in C(0,R), Complex.exp ω*(A+B*ω+C*ω^2)/((ω+z)*ω^3)) =
      A*polarH 2 z+B*polarH 1 z+C*polarH 0 z := by
  by_cases hz : z = 0
  · subst z
    have heq : (fun ω : ℂ => Complex.exp ω*(A+B*ω+C*ω^2)/((ω+0)*ω^3)) =
        (fun ω : ℂ => Complex.exp ω*(A+B*ω+C*ω^2)/ω^4) := by funext ω; ring
    rw [heq]
    exact polar_quadratic_contour_zero A B C R (by simpa using hR)
  · exact polar_quadratic_contour A B C z R hz hR

theorem polarGeneralGeneratorContour_coincident (η : ℝ) (P : Polynomial ℝ)
    (z : ℂ) (innerR outerR : ℝ) (hinner : ‖z‖ < innerR) (houter : ‖z‖ < outerR) :
    polarGeneralGeneratorContour η P ![0,0,-z,0] innerR outerR =
      Complex.exp z*polarPolynomialJ η P z := by
  have hp (ω : ℂ) : (∏ j : Fin 4, (ω- (![0,0,-z,0] : Fin 4 → ℂ) j)) =
      ω^3*(ω+z) := by
    simp only [Fin.prod_univ_succ, Matrix.cons_val_zero,Matrix.cons_val_succ]
    ring
  unfold polarGeneralGeneratorContour
  simp_rw [polarGeneralProfile_coincident η P _ z innerR hinner,hp]
  have heq : (fun ω : ℂ => Complex.exp (ω- (![0,0,-z,0] : Fin 4 → ℂ) 2-
      (![0,0,-z,0] : Fin 4 → ℂ) 3)/(ω^3*(ω+z))*
      (polarPolynomialB η P z+ω*polarPolynomialC η P z)^2) =
      (fun ω : ℂ => Complex.exp z*(Complex.exp ω*
        ((polarPolynomialB η P z)^2+
          (2*polarPolynomialB η P z*polarPolynomialC η P z)*ω+
          (polarPolynomialC η P z)^2*ω^2)/((ω+z)*ω^3))) := by
    funext ω
    change Complex.exp (ω-(-z)-0)/(ω^3*(ω+z))*
      (polarPolynomialB η P z+ω*polarPolynomialC η P z)^2 = _
    rw [sub_neg_eq_add,sub_zero,Complex.exp_add]
    ring
  rw [heq,circleIntegral.integral_const_mul]
  rw [mul_left_comm,polar_quadratic_contour_all _ _ _ z outerR houter]
  rfl

end SixthMoment
