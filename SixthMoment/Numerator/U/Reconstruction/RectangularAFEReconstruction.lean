import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic
import Mathlib.Topology.Algebra.ConstMulAction
import SixthMoment.Arithmetic.QuadraticDivisor.Estimates.Exponents
import SixthMoment.Zeta.AFE.Four.Definitions


namespace SixthMoment

open Complex Source MeasureTheory Set
open scoped BigOperators Topology

noncomputable def rectangularAmplifierPairIntegrand (T : ℝ) (α : MomentShifts)
    (f g Φ : ℝ → ℝ) (u v : ℕ) (t : ℝ) : ℂ :=
  (Φ (t/T) : ℂ)*shiftedFourthProduct t α*
    ((f (Real.log (u+1:ℝ)/Real.log T) : ℂ)/(u+1:ℂ)^criticalLinePoint t)*
    ((g (Real.log (v+1:ℝ)/Real.log T) : ℂ)/(v+1:ℂ)^(1-criticalLinePoint t))

theorem rectangular_twisted_integrand_finite {T : ℝ} (hT : 1 < T) (a b : ℝ)
    (f g Φ : ℝ → ℝ) (hf : ∀ x, a < x → f x = 0) (hg : ∀ x, b < x → g x = 0)
    (α : MomentShifts) (t : ℝ) :
    twistedFourthIntegrand T t α f g Φ =
      ∑ u ∈ Finset.range ⌊T^a⌋₊, ∑ v ∈ Finset.range ⌊T^b⌋₊,
        rectangularAmplifierPairIntegrand T α f g Φ u v t := by
  rw [twistedFourthIntegrand, profileDirichletSum_eq_finite hT a f hf,
    profileDirichletSum_eq_finite hT b g hg]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem rectangular_shifted_product_continuous (α : MomentShifts)
    (hα : ∀ j, ‖α j‖ < 1/4) : Continuous (fun t => shiftedFourthProduct t α) := by
  have hc : ∀ j : Fin 4, Continuous (fun t : ℝ => riemannZeta (sourceZetaPoints t j+α j)) := by
    intro j
    apply continuous_iff_continuousAt.mpr
    intro t
    have hre : (sourceZetaPoints t j).re = 1/2 := by
      fin_cases j <;> norm_num [sourceZetaPoints, criticalLinePoint]
    have hn : sourceZetaPoints t j+α j ≠ 1 := by
      intro hn
      have hr := congrArg Complex.re hn
      have hb := Complex.abs_re_le_norm (α j)
      have ha := hα j
      simp only [add_re, one_re, hre] at hr
      have := (abs_le.mp hb).2
      linarith
    have hpt : ContinuousAt (fun t : ℝ => sourceZetaPoints t j+α j) t := by
      fin_cases j <;> fun_prop [sourceZetaPoints, criticalLinePoint]
    exact (differentiableAt_riemannZeta hn).continuousAt.comp (f := fun t : ℝ => sourceZetaPoints t j+α j) hpt
  convert (((hc 0).mul (hc 1)).mul (hc 2)).mul (hc 3) using 1
  ext t
  simp [shiftedFourthProduct, sourceZetaPoints]

theorem rectangular_scaled_weight_hasCompactSupport {T : ℝ} (hT : T ≠ 0)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    HasCompactSupport (fun t : ℝ => (Φ (t/T) : ℂ)) := by
  have hc : HasCompactSupport Φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hΦ.2
  have hs := hc.comp_smul (inv_ne_zero hT)
  have hs' : HasCompactSupport (fun t : ℝ => Φ (t/T)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hs
  simpa only [Function.comp_def] using hs'.comp_left (show Complex.ofReal 0 = 0 from rfl)

theorem rectangular_amplifier_pair_integrable {T : ℝ} (hT : 1 < T)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ < 1/4) (f g Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) (u v : ℕ) :
    Integrable (rectangularAmplifierPairIntegrand T α f g Φ u v) := by
  have hc : Continuous (rectangularAmplifierPairIntegrand T α f g Φ u v) := by
    change Continuous (fun t : ℝ => (Φ (t/T) : ℂ)*shiftedFourthProduct t α*
      ((f (Real.log (u+1:ℝ)/Real.log T) : ℂ)/(u+1:ℂ)^criticalLinePoint t)*
      ((g (Real.log (v+1:ℝ)/Real.log T) : ℂ)/(v+1:ℂ)^(1-criticalLinePoint t)))
    apply Continuous.mul
    · apply Continuous.mul
      · exact (Complex.continuous_ofReal.comp (hΦ.1.continuous.comp (continuous_id.div_const T))).mul
          (rectangular_shifted_product_continuous α hα)
      · apply Continuous.div continuous_const
        · apply Continuous.const_cpow _ (Or.inl (by exact_mod_cast Nat.succ_ne_zero u))
          fun_prop [criticalLinePoint]
        · intro t
          exact Complex.natCast_add_one_cpow_ne_zero u _
    · apply Continuous.div continuous_const
      · apply Continuous.const_cpow _ (Or.inl (by exact_mod_cast Nat.succ_ne_zero v))
        fun_prop [criticalLinePoint]
      · intro t
        exact Complex.natCast_add_one_cpow_ne_zero v _
  have hs : HasCompactSupport (rectangularAmplifierPairIntegrand T α f g Φ u v) := by
    exact (((rectangular_scaled_weight_hasCompactSupport (ne_of_gt (lt_trans zero_lt_one hT))
      Φ hΦ).mul_right).mul_right).mul_right
  exact hc.integrable_of_hasCompactSupport hs

theorem rectangular_twisted_moment_finite {T : ℝ} (hT : 1 < T) (a b : ℝ)
    (f g Φ : ℝ → ℝ) (hf : ∀ x, a < x → f x = 0) (hg : ∀ x, b < x → g x = 0)
    (hΦ : SmoothDyadicWeight Φ) (α : MomentShifts) (hα : ∀ j, ‖α j‖ < 1/4) :
    twistedFourthMoment T α f g Φ =
      ∑ u ∈ Finset.range ⌊T^a⌋₊, ∑ v ∈ Finset.range ⌊T^b⌋₊,
        ∫ t : ℝ, rectangularAmplifierPairIntegrand T α f g Φ u v t := by
  unfold twistedFourthMoment
  simp_rw [rectangular_twisted_integrand_finite hT a b f g Φ hf hg α]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro u hu
    exact integral_finsetSum _ (fun v _ => rectangular_amplifier_pair_integrable hT α hα f g Φ hΦ u v)
  · intro u hu
    exact integrable_finsetSum _ (fun v _ => rectangular_amplifier_pair_integrable hT α hα f g Φ hΦ u v)

theorem rectangular_twisted_moment_AFE_exact {T : ℝ} (hT : 1 < T) (a b : ℝ)
    (f g Φ : ℝ → ℝ) (hf : ∀ x, a < x → f x = 0) (hg : ∀ x, b < x → g x = 0)
    (hΦ : SmoothDyadicWeight Φ) (α : MomentShifts) (hα : ∀ j, ‖α j‖ < 1/4)
    (G : ℂ → ℂ) :
    twistedFourthMoment T α f g Φ =
      ∑ u ∈ Finset.range ⌊T^a⌋₊, ∑ v ∈ Finset.range ⌊T^b⌋₊,
        ∫ t : ℝ, (Φ (t/T) : ℂ)*
          (bblrAFESum G α t+bblrDualMultiplier t α*bblrAFESum G (bblrSixShifts α 1) t+
            bblrAFEDiscrepancy G α t)*
          ((f (Real.log (u+1:ℝ)/Real.log T) : ℂ)/(u+1:ℂ)^criticalLinePoint t)*
          ((g (Real.log (v+1:ℝ)/Real.log T) : ℂ)/(v+1:ℂ)^(1-criticalLinePoint t)) := by
  rw [rectangular_twisted_moment_finite hT a b f g Φ hf hg hΦ α hα]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro v hv
  apply integral_congr_ae
  filter_upwards [] with t
  dsimp [rectangularAmplifierPairIntegrand, bblrAFEDiscrepancy]
  ring

end SixthMoment
