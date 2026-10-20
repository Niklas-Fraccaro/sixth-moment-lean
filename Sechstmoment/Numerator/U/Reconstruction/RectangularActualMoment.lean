import Mathlib.Tactic
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEError
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEInterchange


namespace Sechstmoment

open Complex Source MeasureTheory Set
open scoped BigOperators Topology
open Classical

noncomputable section

def rectangularMomentPairWeight (T : ℝ) (f g Φ : ℝ → ℝ) (u v : ℕ) (t : ℝ) : ℂ :=
  (Φ (t/T) : ℂ)*
    ((f (Real.log (u+1:ℝ)/Real.log T) : ℂ)/(u+1:ℂ)^criticalLinePoint t)*
    ((g (Real.log (v+1:ℝ)/Real.log T) : ℂ)/(v+1:ℂ)^(1-criticalLinePoint t))

theorem rectangular_moment_pair_weight_continuous (T : ℝ) (f g Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) (u v : ℕ) :
    Continuous (rectangularMomentPairWeight T f g Φ u v) := by
  unfold rectangularMomentPairWeight
  apply Continuous.mul
  · apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (hΦ.1.continuous.comp (continuous_id.div_const T))
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

theorem rectangular_moment_pair_weight_compact {T : ℝ} (hT : T ≠ 0)
    (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (u v : ℕ) :
    HasCompactSupport (rectangularMomentPairWeight T f g Φ u v) :=
  ((rectangular_scaled_weight_hasCompactSupport hT Φ hΦ).mul_right).mul_right

theorem rectangular_dual_multiplier_continuous (α : MomentShifts)
    (hα : ∀ j, |(α j).re| < 1/2) : Continuous (fun t : ℝ => bblrDualMultiplier t α) := by
  unfold bblrDualMultiplier
  apply continuous_finsetProd
  intro j hj
  apply continuous_iff_continuousAt.mpr
  intro t
  have ha := abs_lt.mp (hα j)
  have hstrip : 0 < (sourceZetaPoints t j+α j).re ∧
      (sourceZetaPoints t j+α j).re < 1 := by simp; constructor <;> linarith
  exact (zetaChi_analyticOnNhd_strip _ hstrip).continuousAt.comp
    (f := fun t : ℝ => sourceZetaPoints t j+α j)
    ((rectangular_source_point_continuous j).add continuous_const).continuousAt

theorem rectangular_dual_shifts_strip (α : MomentShifts)
    (hα : ∀ j, |(α j).re| < 1/2) : ∀ j, -1/2 < (bblrSixShifts α 1 j).re := by
  intro j
  fin_cases j <;> simp [bblrSixShifts]
  all_goals linarith [(abs_lt.mp (hα 0)).2, (abs_lt.mp (hα 1)).2,
    (abs_lt.mp (hα 2)).2, (abs_lt.mp (hα 3)).2]

theorem rectangular_pair_AFE_integrable {T : ℝ} (hT : 1 < T) (f g Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) (u v : ℕ) (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, |(α j).re| < 1/2) :
    Integrable (fun t : ℝ => rectangularMomentPairWeight T f g Φ u v t*bblrAFESum G α t) ∧
      Integrable (fun t : ℝ => (rectangularMomentPairWeight T f g Φ u v t*
        bblrDualMultiplier t α)*bblrAFESum G (bblrSixShifts α 1) t) := by
  have hw := rectangular_moment_pair_weight_continuous T f g Φ hΦ u v
  have hs := rectangular_moment_pair_weight_compact (ne_of_gt (lt_trans zero_lt_one hT)) f g Φ hΦ u v
  constructor
  · exact rectangular_actual_AFE_weighted_integrable G α hG
      (fun j => by have := (abs_lt.mp (hα j)).1; linarith) _ hw hs
  · exact rectangular_actual_AFE_weighted_integrable G (bblrSixShifts α 1) hG
      (rectangular_dual_shifts_strip α hα) _
      (hw.mul (rectangular_dual_multiplier_continuous α hα)) hs.mul_right

theorem rectangular_pair_AFE_error_integrable {T : ℝ} (hT : 1 < T) (f g Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) (u v : ℕ) (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, ‖α j‖ < 1/4) :
    Integrable (fun t : ℝ => rectangularMomentPairWeight T f g Φ u v t*
      bblrAFEDiscrepancy G α t) := by
  have ha : ∀ j, |(α j).re| < 1/2 := fun j =>
    lt_trans ((Complex.abs_re_le_norm _).trans_lt (hα j)) (by norm_num)
  obtain ⟨ho, hd⟩ := rectangular_pair_AFE_integrable hT f g Φ hΦ u v G α hG ha
  have hz := rectangular_amplifier_pair_integrable hT α hα f g Φ hΦ u v
  convert hz.sub (ho.add hd) using 1
  ext t
  dsimp [rectangularAmplifierPairIntegrand, rectangularMomentPairWeight, bblrAFEDiscrepancy]
  ring

theorem rectangular_pair_moment_AFE_dyadic {T : ℝ} (hT : 1 < T) (f g Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) (u v : ℕ) (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j, ‖α j‖ < 1/4) :
    (∫ t : ℝ, rectangularAmplifierPairIntegrand T α f g Φ u v t) =
      (∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k, ∫ t : ℝ,
        rectangularMomentPairWeight T f g Φ u v t*bblrAFESummand G α t n)+
      (∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k, ∫ t : ℝ,
        (rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)*
          bblrAFESummand G (bblrSixShifts α 1) t n)+
      ∫ t : ℝ, rectangularMomentPairWeight T f g Φ u v t*bblrAFEDiscrepancy G α t := by
  have ha : ∀ j, |(α j).re| < 1/2 := fun j =>
    lt_trans ((Complex.abs_re_le_norm _).trans_lt (hα j)) (by norm_num)
  have hw := rectangular_moment_pair_weight_continuous T f g Φ hΦ u v
  have hs := rectangular_moment_pair_weight_compact (ne_of_gt (lt_trans zero_lt_one hT)) f g Φ hΦ u v
  obtain ⟨ho, hd⟩ := rectangular_pair_AFE_integrable hT f g Φ hΦ u v G α hG ha
  have he := rectangular_pair_AFE_error_integrable hT f g Φ hΦ u v G α hG hα
  have hohd : Integrable (fun t : ℝ =>
      rectangularMomentPairWeight T f g Φ u v t*bblrAFESum G α t+
        (rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)*
          bblrAFESum G (bblrSixShifts α 1) t) := ho.add hd
  have hp : rectangularAmplifierPairIntegrand T α f g Φ u v = fun t : ℝ =>
      (rectangularMomentPairWeight T f g Φ u v t*bblrAFESum G α t+
        (rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)*
          bblrAFESum G (bblrSixShifts α 1) t)+
        rectangularMomentPairWeight T f g Φ u v t*bblrAFEDiscrepancy G α t := by
    ext t
    dsimp [rectangularAmplifierPairIntegrand, rectangularMomentPairWeight, bblrAFEDiscrepancy]
    ring
  rw [hp]
  dsimp only
  rw [integral_add hohd he, integral_add ho hd,
    rectangular_actual_AFE_dyadic_integral G α hG (fun j => by have := (abs_lt.mp (ha j)).1; linarith) _ hw hs,
    rectangular_actual_AFE_dyadic_integral G (bblrSixShifts α 1) hG
      (rectangular_dual_shifts_strip α ha)
      (fun t : ℝ => rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)
      (hw.mul (rectangular_dual_multiplier_continuous α ha)) hs.mul_right]

def rectangularOriginalAFEBlocks (T : ℝ) (α : MomentShifts) (G : ℂ → ℂ)
    (f g Φ : ℝ → ℝ) (u v : ℕ) : ℂ :=
  ∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k, ∫ t : ℝ,
    rectangularMomentPairWeight T f g Φ u v t*bblrAFESummand G α t n

def rectangularDualAFEBlocks (T : ℝ) (α : MomentShifts) (G : ℂ → ℂ)
    (f g Φ : ℝ → ℝ) (u v : ℕ) : ℂ :=
  ∑' k : Fin 4 → ℕ, ∑ n ∈ rectangularAFEDyadicBox k, ∫ t : ℝ,
    (rectangularMomentPairWeight T f g Φ u v t*bblrDualMultiplier t α)*
      bblrAFESummand G (bblrSixShifts α 1) t n

def rectangularActualAFEBlocks (T a b : ℝ) (α : MomentShifts) (G : ℂ → ℂ)
    (f g Φ : ℝ → ℝ) : ℂ :=
  ∑ u ∈ Finset.range ⌊T^a⌋₊, ∑ v ∈ Finset.range ⌊T^b⌋₊,
    (rectangularOriginalAFEBlocks T α G f g Φ u v+
      rectangularDualAFEBlocks T α G f g Φ u v)

theorem rectangular_AFE_error_integrand_finite {T : ℝ} (hT : 1 < T) (a b : ℝ)
    (f g Φ : ℝ → ℝ) (hf : ∀ x, a < x → f x = 0) (hg : ∀ x, b < x → g x = 0)
    (α : MomentShifts) (G : ℂ → ℂ) (t : ℝ) :
    rectangularAFEErrorIntegrand T α G f g Φ t =
      ∑ u ∈ Finset.range ⌊T^a⌋₊, ∑ v ∈ Finset.range ⌊T^b⌋₊,
        rectangularMomentPairWeight T f g Φ u v t*bblrAFEDiscrepancy G α t := by
  rw [rectangularAFEErrorIntegrand, profileDirichletSum_eq_finite hT a f hf,
    profileDirichletSum_eq_finite hT b g hg]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem rectangular_AFE_error_integral_finite {T : ℝ} (hT : 1 < T) (a b : ℝ)
    (f g Φ : ℝ → ℝ) (hf : ∀ x, a < x → f x = 0) (hg : ∀ x, b < x → g x = 0)
    (hΦ : SmoothDyadicWeight Φ) (α : MomentShifts) (G : ℂ → ℂ)
    (hG : BBLREntireWeight G α) (hα : ∀ j, ‖α j‖ < 1/4) :
    rectangularAFEIntegratedError T α G f g Φ =
      ∑ u ∈ Finset.range ⌊T^a⌋₊, ∑ v ∈ Finset.range ⌊T^b⌋₊,
        ∫ t : ℝ, rectangularMomentPairWeight T f g Φ u v t*bblrAFEDiscrepancy G α t := by
  unfold rectangularAFEIntegratedError
  simp_rw [rectangular_AFE_error_integrand_finite hT a b f g Φ hf hg α G]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro u hu
    exact integral_finsetSum _ (fun v _ => rectangular_pair_AFE_error_integrable hT f g Φ hΦ u v G α hG hα)
  · intro u hu
    exact integrable_finsetSum _ (fun v _ => rectangular_pair_AFE_error_integrable hT f g Φ hΦ u v G α hG hα)

theorem rectangular_actual_moment_AFE_reconstruction {T : ℝ} (hT : 1 < T) (a b : ℝ)
    (f g Φ : ℝ → ℝ) (hf : ∀ x, a < x → f x = 0) (hg : ∀ x, b < x → g x = 0)
    (hΦ : SmoothDyadicWeight Φ) (α : MomentShifts) (G : ℂ → ℂ)
    (hG : BBLREntireWeight G α) (hα : ∀ j, ‖α j‖ < 1/4) :
    twistedFourthMoment T α f g Φ = rectangularActualAFEBlocks T a b α G f g Φ+
      rectangularAFEIntegratedError T α G f g Φ := by
  rw [rectangular_twisted_moment_finite hT a b f g Φ hf hg hΦ α hα,
    rectangular_AFE_error_integral_finite hT a b f g Φ hf hg hΦ α G hG hα]
  simp_rw [rectangular_pair_moment_AFE_dyadic hT f g Φ hΦ _ _ G α hG hα]
  simp only [rectangularActualAFEBlocks, rectangularOriginalAFEBlocks, rectangularDualAFEBlocks,
    Finset.sum_add_distrib]

theorem rectangular_actual_moment_discrepancy_AFE {T : ℝ} (hT : 1 < T) (a b : ℝ)
    (f g Φ : ℝ → ℝ) (hf : ∀ x, a < x → f x = 0) (hg : ∀ x, b < x → g x = 0)
    (hΦ : SmoothDyadicWeight Φ) (α : MomentShifts) (G : ℂ → ℂ)
    (hG : BBLREntireWeight G α) (hα : ∀ j, ‖α j‖ < 1/4) :
    bblrMomentDiscrepancy T a b α G f g Φ =
      (rectangularActualAFEBlocks T a b α G f g Φ-bblrSixMainTerms T a b α G f g Φ)+
        rectangularAFEIntegratedError T α G f g Φ := by
  rw [bblrMomentDiscrepancy,
    rectangular_actual_moment_AFE_reconstruction hT a b f g Φ hf hg hΦ α G hG hα]
  ring

end
end Sechstmoment
