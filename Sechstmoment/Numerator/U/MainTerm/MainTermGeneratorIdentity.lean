import Sechstmoment.Numerator.U.MainTerm.CompactSixGenerator
import Sechstmoment.Numerator.U.MainTerm.PrincipalProfileKernelInversion
import Sechstmoment.Numerator.U.MainTerm.SixPrincipalLimit

/-! Genuine identification of the actual six principal Mellin limits with the entire
regular profile generator.  The proof evaluates all six contour kernels and uses the
literal six-term alternant identity; it introduces no analytical target premise. -/

namespace Sechstmoment
open Complex Real MeasureTheory Set Source
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1000000

private theorem bblrSixShifts_pairs_distinct
    (σ : MomentShifts) (hσ : Function.Injective (polarSourceKnots σ)) (m : Fin 6) :
    bblrSixShifts σ m 0 ≠ bblrSixShifts σ m 1 ∧
      bblrSixShifts σ m 2 ≠ bblrSixShifts σ m 3 := by
  have h01 : -σ 0 ≠ -σ 1 := hσ.ne (show (0:Fin 4) ≠ 1 by decide)
  have h02 : -σ 0 ≠ σ 2 := hσ.ne (show (0:Fin 4) ≠ 2 by decide)
  have h03 : -σ 0 ≠ σ 3 := hσ.ne (show (0:Fin 4) ≠ 3 by decide)
  have h12 : -σ 1 ≠ σ 2 := hσ.ne (show (1:Fin 4) ≠ 2 by decide)
  have h13 : -σ 1 ≠ σ 3 := hσ.ne (show (1:Fin 4) ≠ 3 by decide)
  have h23 : σ 2 ≠ σ 3 := hσ.ne (show (2:Fin 4) ≠ 3 by decide)
  fin_cases m
  · simpa [bblrSixShifts] using And.intro h01 h23
  · simpa [bblrSixShifts] using And.intro h23 h01
  · constructor
    · intro hz
      apply h12
      norm_num [bblrSixShifts] at hz
      linear_combination hz
    · simpa [bblrSixShifts] using h03
  · constructor
    · intro hz
      apply h13
      norm_num [bblrSixShifts] at hz
      linear_combination hz
    · simpa [bblrSixShifts] using h02.symm
  · constructor
    · intro hz
      apply h02
      norm_num [bblrSixShifts] at hz
      linear_combination -hz
    · simpa [bblrSixShifts] using h13
  · constructor
    · intro hz
      apply h03
      norm_num [bblrSixShifts] at hz
      linear_combination -hz
    · simpa [bblrSixShifts] using h12.symm

/-- The actual normalized principal limit is the regular source-profile generator.
The separated-shift hypothesis is used to evaluate the six literal rational terms;
the right side is already entire and therefore supplies the collision continuation. -/
theorem actualSixPrincipalPolarLimit_eq_regularProfileGenerator
    (σ : MomentShifts) (hσ : Function.Injective (polarSourceKnots σ))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f g : ℝ → ℂ) (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    (hfsupp : ∀ x ∉ Icc 0 a, f x = 0) (hgsupp : ∀ y ∉ Icc 0 b, g y = 0)
    (Φ : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hshift : ∀ m : Fin 6, ∀ j : Fin 4, 0 < c + (bblrSixShifts σ m j).re) :
    actualSixPrincipalPolarLimit σ f g Φ c =
      actualRegularProfileGenerator a b f g Φ σ := by
  unfold actualSixPrincipalPolarLimit
  have hkernel (m : Fin 6) := actualPrincipalPolarLimitKernel_profile_inversion
    σ m a b ha hb f g hf hfs hg hgs hfsupp hgsupp c hc (hshift m)
    (bblrSixShifts_pairs_distinct σ hσ m).1 (bblrSixShifts_pairs_distinct σ hσ m).2
  simp_rw [hkernel]
  rw [actualRegularProfileGenerator_eq_compact_six_factored a b f g Φ
    hfs.continuous hgs.continuous σ hσ]
  simp_rw [intervalIntegral.integral_div]
  have hp (α : MomentShifts) : principalPurePolarProduct α =
      (α 0+α 2)*(α 0+α 3)*(α 1+α 2)*(α 1+α 3) := by
    norm_num [principalPurePolarProduct, Fin.prod_univ_succ]
    ring
  simp_rw [hp]
  have hterm (e z p : ℂ) : e*((arithmeticFactor:ℂ)*(z/p)) =
      (arithmeticFactor:ℂ)*(e*z/p) := by ring
  simp_rw [hterm, ← Finset.mul_sum]
  ring

end
end Sechstmoment
