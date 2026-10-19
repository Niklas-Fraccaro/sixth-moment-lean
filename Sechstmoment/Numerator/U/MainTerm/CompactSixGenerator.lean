import Sechstmoment.Numerator.U.MainTerm.RegularProfileGenerator
import Sechstmoment.Numerator.U.MainTerm.SixTermAlternant

/-! Compact integral identification of the literal six convolution terms with the regular,
collision-safe profile generator. All finite-sum interchanges are proved from continuity. -/

namespace Sechstmoment
open Complex MeasureTheory Set Source
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem bblrExponentialConvolutionPoleTerm_continuous
    (σ : MomentShifts) (m : Fin 6) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      bblrExponentialConvolutionPoleTerm σ p.1 p.2.1 p.2.2 m) := by
  unfold bblrExponentialConvolutionPoleTerm exponentialDifference
  fun_prop

theorem bblrExponentialConvolutionIntegral_continuous
    (σ : MomentShifts) (m : Fin 6) :
    Continuous (fun p : ℝ × ℝ =>
      ∫ t in (0:ℝ)..min p.1 p.2, bblrExponentialConvolutionPoleTerm σ p.1 p.2 t m) := by
  have hmap : Continuous (fun p : (ℝ × ℝ) × ℝ => (p.1.1,p.1.2,p.2)) := by fun_prop
  have hjoint : Continuous (fun p : (ℝ × ℝ) × ℝ =>
      bblrExponentialConvolutionPoleTerm σ p.1.1 p.1.2 p.2 m) := by
    simpa only [Function.comp_def] using
      (bblrExponentialConvolutionPoleTerm_continuous σ m).comp hmap
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (μ := (volume : Measure ℝ)) (a₀ := (0:ℝ))
    (f := fun (p : ℝ × ℝ) (t : ℝ) =>
      bblrExponentialConvolutionPoleTerm σ p.1 p.2 t m)
    (s := fun p : ℝ × ℝ => min p.1 p.2)
    hjoint (continuous_fst.min continuous_snd)

/-- The regularized alternant equals the finite sum of compact positive-convolution terms
on the separated locus. -/
theorem actualRegularProfileKernel_eq_six_integrals
    (σ : MomentShifts) (hσ : Function.Injective (polarSourceKnots σ)) (A B : ℝ) :
    actualRegularProfileKernel σ A B =
      ∑ m : Fin 6, ∫ t in (0:ℝ)..min A B,
        bblrExponentialConvolutionPoleTerm σ A B t m := by
  unfold actualRegularProfileKernel
  simp_rw [exponentialAlternantRegularized_eq_raw _ _ hσ,
    ← bblrSixExponentialConvolution_eq_alternant σ hσ]
  exact intervalIntegral.integral_finsetSum (fun m _ =>
    ((bblrExponentialConvolutionPoleTerm_continuous σ m).comp
      (by fun_prop : Continuous (fun t : ℝ => (A,B,t)))).intervalIntegrable _ _)

/-- Integrated six-term identity.  It identifies the actual finite sum, retaining the
arithmetic and weight factors, with the entire regular profile generator. -/
theorem actualRegularProfileGenerator_eq_compact_six
    (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (σ : MomentShifts) (hσ : Function.Injective (polarSourceKnots σ)) :
    actualRegularProfileGenerator a b f g Φ σ =
      (arithmeticFactor:ℂ) * (∫ x, (Φ x:ℂ)) *
        ∑ m : Fin 6, ∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
          f A * g B * ∫ t in (0:ℝ)..min A B,
            bblrExponentialConvolutionPoleTerm σ A B t m := by
  unfold actualRegularProfileGenerator
  congr 1
  simp_rw [actualRegularProfileKernel_eq_six_integrals σ hσ, Finset.mul_sum]
  have hinner (A : ℝ) :
      (∫ B in (0:ℝ)..b, ∑ m : Fin 6,
        f A * g B * ∫ t in (0:ℝ)..min A B,
          bblrExponentialConvolutionPoleTerm σ A B t m) =
        ∑ m : Fin 6, ∫ B in (0:ℝ)..b,
          f A * g B * ∫ t in (0:ℝ)..min A B,
            bblrExponentialConvolutionPoleTerm σ A B t m := by
    apply intervalIntegral.integral_finsetSum
    intro m _
    exact ((continuous_const.mul hg).mul
      ((bblrExponentialConvolutionIntegral_continuous σ m).comp
        (by fun_prop : Continuous (fun B : ℝ => (A,B))))).intervalIntegrable _ _
  simp_rw [hinner]
  apply intervalIntegral.integral_finsetSum
  intro m _
  apply Continuous.intervalIntegrable
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((hf.comp continuous_fst).mul (hg.comp continuous_snd)).mul
    (bblrExponentialConvolutionIntegral_continuous σ m)

/-- Pulling out the source phase and the four pure poles produces exactly the usual
compact two-profile expression. -/
theorem bblrExponentialConvolution_compact_integral_factored
    (a b : ℝ) (f g : ℝ → ℂ) (σ : MomentShifts) (m : Fin 6) :
    (∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
      f A * g B * ∫ t in (0:ℝ)..min A B,
        bblrExponentialConvolutionPoleTerm σ A B t m) =
      Complex.exp (bblrSixPhaseExponents σ m) *
        (∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
          f A * g B * ∫ t in (0:ℝ)..min A B,
            exponentialDifference (bblrSixShifts σ m 2) (bblrSixShifts σ m 3) (A-t) *
            exponentialDifference (bblrSixShifts σ m 0) (bblrSixShifts σ m 1) (B-t)) /
        ((bblrSixShifts σ m 0 + bblrSixShifts σ m 2)*
          (bblrSixShifts σ m 0 + bblrSixShifts σ m 3)*
          (bblrSixShifts σ m 1 + bblrSixShifts σ m 2)*
          (bblrSixShifts σ m 1 + bblrSixShifts σ m 3)) := by
  let c := Complex.exp (bblrSixPhaseExponents σ m) /
    ((bblrSixShifts σ m 0 + bblrSixShifts σ m 2)*
      (bblrSixShifts σ m 0 + bblrSixShifts σ m 3)*
      (bblrSixShifts σ m 1 + bblrSixShifts σ m 2)*
      (bblrSixShifts σ m 1 + bblrSixShifts σ m 3))
  have hterm (A B t : ℝ) : bblrExponentialConvolutionPoleTerm σ A B t m =
      c * (exponentialDifference (bblrSixShifts σ m 2) (bblrSixShifts σ m 3) (A-t) *
        exponentialDifference (bblrSixShifts σ m 0) (bblrSixShifts σ m 1) (B-t)) := by
    dsimp [bblrExponentialConvolutionPoleTerm, c]
    ring
  simp_rw [hterm, intervalIntegral.integral_const_mul]
  have hmul (A B : ℝ) (z : ℂ) : f A * g B * (c*z) = c * (f A*g B*z) := by ring
  simp_rw [hmul, intervalIntegral.integral_const_mul]
  dsimp only [c]
  ring

/-- The fully factored compact six-term main limit equals the regular entire generator.
Pole separation is required only for the algebraic comparison. -/
theorem actualRegularProfileGenerator_eq_compact_six_factored
    (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (σ : MomentShifts) (hσ : Function.Injective (polarSourceKnots σ)) :
    actualRegularProfileGenerator a b f g Φ σ =
      (arithmeticFactor:ℂ) * (∫ x, (Φ x:ℂ)) *
        ∑ m : Fin 6, Complex.exp (bblrSixPhaseExponents σ m) *
          (∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
            f A * g B * ∫ t in (0:ℝ)..min A B,
              exponentialDifference (bblrSixShifts σ m 2) (bblrSixShifts σ m 3) (A-t) *
              exponentialDifference (bblrSixShifts σ m 0) (bblrSixShifts σ m 1) (B-t)) /
          ((bblrSixShifts σ m 0 + bblrSixShifts σ m 2)*
            (bblrSixShifts σ m 0 + bblrSixShifts σ m 3)*
            (bblrSixShifts σ m 1 + bblrSixShifts σ m 2)*
            (bblrSixShifts σ m 1 + bblrSixShifts σ m 3)) := by
  rw [actualRegularProfileGenerator_eq_compact_six a b f g Φ hf hg σ hσ]
  simp_rw [bblrExponentialConvolution_compact_integral_factored]

end
end Sechstmoment
