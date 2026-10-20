import Sechstmoment.Numerator.V.Chi.LogBandDerivatives
import Sechstmoment.Numerator.V.Chi.LogBandMask


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped ContDiff BigOperators
noncomputable section

theorem noDPLogBandProfile_uniform_derivatives (h : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ c ∈ Icc (1:ℝ) 2, ∀ u,
      ‖iteratedDeriv n (noDPLogBandProfile h T c) u‖ ≤ C*T^(n+1) := by
  obtain ⟨A,hA,hamp⟩ := noDPLogBandAmplitude_uniform_derivatives
  choose B hB hb using (fun j : ℕ => schwartz_scaled_log_derivative_bound h j)
  have hB0 (j : ℕ) : 0 ≤ B j := (hB j).le
  let D := a03ProfileProductDerivativeBudget A B n
  have hD : 0 ≤ D := by
    dsimp only [D,a03ProfileProductDerivativeBudget]
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB0 _))
  refine ⟨D+1,by positivity,?_⟩
  intro T hT c hc u
  have hT0 : 0 < T := by linarith
  have ha : 0 < T/(2*Real.pi) := by positivity
  have haT : T/(2*Real.pi) ≤ T :=
    div_le_self hT0.le (by linarith [Real.two_le_pi])
  let f : ℝ → ℂ := fun y => h (-T*Real.log y/(2*Real.pi))
  have hf (y : ℝ) (hy : y ∈ Icc (3/4:ℝ) (5/4)) : ContDiffAt ℝ ∞ f y := by
    have hy0 : 0 < y := by linarith [hy.1]
    exact h.smooth'.contDiffAt.comp y
      ((contDiffAt_const.mul (Real.contDiffAt_log.mpr hy0.ne')).div_const _)
  have hfd (j : ℕ) (_hj : j ≤ n) (y : ℝ) (hy : y ∈ Icc (3/4:ℝ) (5/4)) :
      ‖iteratedDeriv j f y‖ ≤ B j*T^j := hb j T hT y hy
  have hprod := compact_derivative_product_bound (noDPLogBandAmplitude_contDiff c)
    hT (noDPLogBandAmplitude_tsupport c) hf hA hB0 (hamp c hc) n hfd u
  have he : noDPLogBandProfile h T c = fun y : ℝ =>
      ((T/(2*Real.pi):ℝ):ℂ)*a03ProfileProduct (noDPLogBandAmplitude c) f y := by
    funext y
    rw [noDPLogBandProfile_eq_amplitude]
    dsimp only [a03ProfileProduct,f]
    ring
  rw [he,iteratedDeriv_const_mul_field,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos ha]
  calc
    _ ≤ T*(D*T^n) := mul_le_mul haT hprod (norm_nonneg _) hT0.le
    _ = D*T^(n+1) := by rw [pow_succ]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hT0.le _)

theorem noDPLogBandProfile_uniform_derivative_mass (h : SchwartzMap ℝ ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ c ∈ Icc (1:ℝ) 2,
      (∫ u : ℝ, ‖iteratedDeriv n (noDPLogBandProfile h T c) u‖) ≤ C*T^(n+1) := by
  obtain ⟨C,hC,hbound⟩ := noDPLogBandProfile_uniform_derivatives h n
  refine ⟨C,hC,?_⟩
  intro T hT c hc
  have hT0 : 0 < T := by linarith
  let M := C*T^(n+1)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  let g : ℝ → ℝ := (Icc (3/4:ℝ) (5/4)).indicator (fun _ => M)
  have hiconst : IntegrableOn (fun _ : ℝ => M) (Icc (3/4:ℝ) (5/4)) :=
    (continuous_const : Continuous (fun _ : ℝ => M)).continuousOn.integrableOn_Icc
  have hi : Integrable g :=
    (integrable_indicator_iff measurableSet_Icc).mpr hiconst
  have hpoint (u : ℝ) : ‖iteratedDeriv n (noDPLogBandProfile h T c) u‖ ≤ g u := by
    by_cases hu : u ∈ Icc (3/4:ℝ) (5/4)
    · simpa only [g,Set.indicator_of_mem hu] using hbound T hT c hc u
    · have hz : iteratedDeriv n (noDPLogBandProfile h T c) u = 0 := by
        apply Function.notMem_support.mp
        intro hm
        exact hu (noDPLogBandProfile_tsupport h T c
          (a03_iteratedDeriv_tsupport_subset (noDPLogBandProfile h T c) n (subset_tsupport _ hm)))
      simp only [g,Set.indicator_of_notMem hu,hz,norm_zero]
      exact le_rfl
  have H := integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => norm_nonneg
    (iteratedDeriv n (noDPLogBandProfile h T c) u))) hi (Filter.Eventually.of_forall hpoint)
  dsimp only [g] at H
  rw [integral_indicator measurableSet_Icc,setIntegral_const] at H
  norm_num [Real.volume_Icc,smul_eq_mul] at H
  exact H.trans (by nlinarith)

end
end Sechstmoment.Source
