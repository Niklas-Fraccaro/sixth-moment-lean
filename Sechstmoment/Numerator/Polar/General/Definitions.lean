import Mathlib.Algebra.Polynomial.Eval.Defs
import Sechstmoment.Numerator.Polar.Generator.Inversion

namespace Sechstmoment
open scoped BigOperators

noncomputable def polarTripleInverseContour (x : ℝ) (q : Fin 3 → ℂ) (R : ℝ) : ℂ :=
  (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
    ∮ u in C(0,R), Complex.exp ((x:ℂ)*u)/(∏ j : Fin 3, (u-q j))

noncomputable def polarGeneralInverseContour (x : ℝ) (ω : ℂ) (q : Fin 4 → ℂ) (R : ℝ) : ℂ :=
  (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
    ∮ u in C(0,R), Complex.exp ((x:ℂ)*u)*(u-ω)/(∏ j : Fin 4, (u-q j))

noncomputable def polarGeneralProfile (η : ℝ) (P : Polynomial ℝ)
    (q : Fin 4 → ℂ) (R : ℝ) (ω : ℂ) : ℂ :=
  ∫ a in (0:ℝ)..η, ((Polynomial.eval (1-a/η : ℝ) P : ℝ):ℂ)*polarGeneralInverseContour a ω q R

noncomputable def polarGeneralTripleProfile (η : ℝ) (P : Polynomial ℝ)
    (q : Fin 3 → ℂ) (R : ℝ) : ℂ :=
  ∫ a in (0:ℝ)..η, ((Polynomial.eval (1-a/η : ℝ) P : ℝ):ℂ)*polarTripleInverseContour a q R

noncomputable def polarGeneralGeneratorContour (η : ℝ) (P : Polynomial ℝ)
    (q : Fin 4 → ℂ) (innerR outerR : ℝ) : ℂ :=
  (2*(Real.pi:ℂ)*Complex.I)⁻¹ *
    ∮ ω in C(0,outerR), Complex.exp (ω-q 2-q 3) /
      (∏ j : Fin 4, (ω-q j)) * (polarGeneralProfile η P q innerR ω)^2

end Sechstmoment
