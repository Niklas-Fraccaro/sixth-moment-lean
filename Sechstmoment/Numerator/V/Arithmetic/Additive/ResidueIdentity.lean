import Sechstmoment.Numerator.V.Arithmetic.Additive.MellinIdentity
import Sechstmoment.Numerator.V.Arithmetic.CorrectedMellinContour


namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory ZMod
open scoped BigOperators ContDiff
noncomputable section
set_option autoImplicit false

def divisorPrincipalResidues (N : ℕ) (hN : N ≠ 0) (d : N.divisors)
    (w : ℝ → ℂ) (β : Fin 4 → ℂ) (x : ℝ) : ℂ :=
  let _ : NeZero (N/d.val) := divisorQuotientNeZero N hN d
  ((N/d.val).totient:ℂ)⁻¹*(ArithmeticFunction.moebius (N/d.val):ℂ)*
    principalMellinResidueSum (N/d.val) d.val w β (x/d.val)

theorem divisorMellinIntegral_contour_shift {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (N : ℕ) (hN : N ≠ 0) (d : N.divisors)
    (β : Fin 4 → ℂ) (hsep : Function.Injective β) {x a b : ℝ}
    (hx : 0 < x) (ha : 1/2 < a) (hb : b ≤ 5/4)
    (hβ : ∀ j, ‖β j‖ ≤ min (1/8) (a-1/2))
    (hpa : ∀ j, a < (1-β j).re) (hpb : ∀ j, (1-β j).re < b) :
    divisorMellinIntegral N hN d w b β x =
      divisorMellinIntegral N hN d w a β x+
        (2*Real.pi:ℂ)*divisorPrincipalResidues N hN d w β x := by
  let : NeZero (N/d.val) := divisorQuotientNeZero N hN d
  have hd : d.val ≠ 0 := NoDPGlobalConvolution.divisor_ne_zero d.property
  have hdp : (0:ℝ) < d.val := by exact_mod_cast Nat.pos_of_ne_zero hd
  have H := correctedMellin_contour_shift hw hws (N/d.val) d.val hd β hsep
    (div_pos hx hdp) ha hb hβ hpa hpb
  simpa only [divisorMellinIntegral,divisorPrincipalResidues,mul_assoc] using H

theorem additive_fourAF_residue_identity {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (N : ℕ) (hN : N ≠ 0) (β : Fin 4 → ℂ) (hsep : Function.Injective β)
    {x a b : ℝ} (hx : 0 < x) (ha : 1/2 < a) (hb : b ≤ 5/4)
    (hβ : ∀ j, ‖β j‖ ≤ min (1/8) (a-1/2))
    (hpa : ∀ j, a < (1-β j).re) (hc : ∀ j, 1 < b+(β j).re) :
    (∑' m : ℕ, (fourAF β m*w ((m:ℝ)/x))*naturalAdditivePhase N m) =
      (1/(2*Real.pi):ℂ)*(∑ d : N.divisors, divisorMellinIntegral N hN d w a β x)+
        ∑ d : N.divisors, divisorPrincipalResidues N hN d w β x := by
  have hpb (j : Fin 4) : (1-β j).re < b := by
    simp only [sub_re,one_re]
    linarith [hc j]
  rw [additive_fourAF_mellin_identity hw hws N hN β b hc hx]
  simp_rw [divisorMellinIntegral_contour_shift hw hws N hN _ β hsep hx ha hb hβ hpa hpb]
  rw [Finset.sum_add_distrib,← Finset.mul_sum,mul_add]
  have hπ : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2*Real.pi:ℝ) ≠ 0)
  congr 1
  field_simp [hπ]

end
end Sechstmoment.Source.NoDPGlobalLFactorization
