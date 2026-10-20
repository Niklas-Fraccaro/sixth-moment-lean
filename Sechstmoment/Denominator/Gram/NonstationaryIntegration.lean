import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace


namespace Sechstmoment
open Complex Real MeasureTheory Set
open scoped ContDiff BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def d06NonstationaryAmplitude (A r : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => A
  | k + 1 => deriv (fun x => d06NonstationaryAmplitude A r k x * r x)

def d06NonstationaryBudget (C B : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, j => C j
  | k + 1, j => ∑ i ∈ Finset.range (j + 2),
      ((j + 1).choose i : ℝ) * d06NonstationaryBudget C B k i * B (j + 1 - i)

theorem d06_supported_product_contDiff {A r : ℝ → ℂ}
    (hA : ContDiff ℝ ∞ A)
    (hr : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ r x) :
    ContDiff ℝ ∞ (fun x => A x * r x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport A
  · exact hA.contDiffAt.mul (hr x hx)
  · have he : (fun y => A y * r y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport A).isOpen_compl.mem_nhds hx] with y hy
      have hz : A y = 0 := Function.notMem_support.mp (fun hs => hy (subset_tsupport A hs))
      simp [hz]
    exact contDiffAt_const.congr_of_eventuallyEq he

theorem d06_nonstationary_amplitude_support (A r : ℝ → ℂ) (k : ℕ) :
    tsupport (d06NonstationaryAmplitude A r k) ⊆ tsupport A := by
  induction k with
  | zero => exact subset_rfl
  | succ k hk =>
      exact tsupport_deriv_subset.trans (tsupport_mul_subset_left.trans hk)

theorem d06_nonstationary_amplitude_contDiff {A r : ℝ → ℂ}
    (hA : ContDiff ℝ ∞ A)
    (hr : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ r x) (k : ℕ) :
    ContDiff ℝ ∞ (d06NonstationaryAmplitude A r k) := by
  induction k with
  | zero => exact hA
  | succ k hk =>
      exact (contDiff_infty_iff_deriv.mp
        (d06_supported_product_contDiff hk
          (fun x hx => hr x (d06_nonstationary_amplitude_support A r k hx)))).2

theorem d06_nonstationary_budget_nonneg {C B : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (hB : ∀ j, 0 ≤ B j) (k j : ℕ) :
    0 ≤ d06NonstationaryBudget C B k j := by
  induction k generalizing j with
  | zero => exact hC j
  | succ k hk =>
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hk i)) (hB _)

theorem d06_nonstationary_amplitude_derivative_bound {A r : ℝ → ℂ}
    (hA : ContDiff ℝ ∞ A)
    (hr : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ r x)
    {C B : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (hB : ∀ j, 0 ≤ B j)
    (hAd : ∀ j x, ‖iteratedDeriv j A x‖ ≤ C j)
    (hrd : ∀ j x, x ∈ tsupport A → ‖iteratedDeriv j r x‖ ≤ B j)
    (k j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j (d06NonstationaryAmplitude A r k) x‖ ≤
      d06NonstationaryBudget C B k j := by
  induction k generalizing j with
  | zero => exact hAd j x
  | succ k hk =>
      by_cases hx : x ∈ tsupport A
      · have hAk := d06_nonstationary_amplitude_contDiff hA hr k
        change ‖iteratedDeriv j (deriv (fun x => d06NonstationaryAmplitude A r k x * r x)) x‖ ≤ _
        rw [← iteratedDeriv_succ', iteratedDeriv_fun_mul
          (hAk.contDiffAt.of_le (by simp)) ((hr x hx).of_le (by simp))]
        calc
          _ ≤ ∑ i ∈ Finset.range (j + 1 + 1),
              ‖((j + 1).choose i : ℂ) * iteratedDeriv i
                (d06NonstationaryAmplitude A r k) x * iteratedDeriv (j + 1 - i) r x‖ :=
            norm_sum_le _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hi
            simp only [norm_mul, Complex.norm_natCast]
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (hk i) (Nat.cast_nonneg _)
            · exact hrd _ x hx
            · exact norm_nonneg _
            · exact mul_nonneg (Nat.cast_nonneg _) (d06_nonstationary_budget_nonneg hC hB k i)
      · have hs : tsupport (iteratedDeriv j (d06NonstationaryAmplitude A r (k + 1))) ⊆ tsupport A := by
          apply subset_trans _ (d06_nonstationary_amplitude_support A r (k + 1))
          induction j with
          | zero => simp
          | succ j hj => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans hj
        have hz : iteratedDeriv j (d06NonstationaryAmplitude A r (k + 1)) x = 0 :=
          Function.notMem_support.mp (fun hh => hx (hs (subset_tsupport _ hh)))
        rw [hz, norm_zero]
        exact d06_nonstationary_budget_nonneg hC hB _ _

theorem d06_supported_product_integrable {A E : ℝ → ℂ}
    (hA : ContDiff ℝ ∞ A) (hs : tsupport A ⊆ Icc (1 : ℝ) 2)
    (hE : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ E x) :
    Integrable (fun x => A x * E x) := by
  apply (d06_supported_product_contDiff hA hE).continuous.integrable_of_hasCompactSupport
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_mul_subset_left.trans hs)

theorem d06_nonstationary_one_step {A r E w : ℝ → ℂ} {T : ℝ}
    (hT : T ≠ 0) (hA : ContDiff ℝ ∞ A) (hs : tsupport A ⊆ Icc (1 : ℝ) 2)
    (hr : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ r x)
    (hE : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ E x)
    (hEd : ∀ x ∈ tsupport A, HasDerivAt E ((T : ℂ) * w x * E x) x)
    (hinv : ∀ x ∈ tsupport A, r x * w x = 1) :
    (∫ x : ℝ, A x * E x) =
      -(T : ℂ)⁻¹ * ∫ x : ℝ, deriv (fun y => A y * r y) x * E x := by
  let u : ℝ → ℂ := fun x => A x * r x
  have huS : ContDiff ℝ ∞ u := d06_supported_product_contDiff hA hr
  have huSupp : tsupport u ⊆ tsupport A := tsupport_mul_subset_left
  have huDerivSupp : tsupport (deriv u) ⊆ tsupport A := tsupport_deriv_subset.trans huSupp
  have hAE := d06_supported_product_integrable hA hs hE
  have hDE := d06_supported_product_integrable (contDiff_infty_iff_deriv.mp huS).2
    (huDerivSupp.trans hs) (fun x hx => hE x (huDerivSupp hx))
  have huE := d06_supported_product_integrable huS (huSupp.trans hs)
    (fun x hx => hE x (huSupp hx))
  have heq : (fun x => u x * ((T : ℂ) * w x * E x)) =
      (fun x => (T : ℂ) * (A x * E x)) := by
    funext x
    by_cases hx : x ∈ tsupport A
    · dsimp [u]
      calc
        A x * r x * ((T : ℂ) * w x * E x) = (T : ℂ) * (A x * E x) * (r x * w x) := by ring
        _ = _ := by rw [hinv x hx, mul_one]
    · have hz : A x = 0 := Function.notMem_support.mp (fun hh => hx (subset_tsupport A hh))
      simp [u, hz]
  have hI := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := u) (v := E) (u' := deriv u) (v' := fun x => (T : ℂ) * w x * E x)
    (fun x _ => huS.differentiable (by simp) x |>.hasDerivAt)
    (fun x hx => hEd x (huSupp hx))
    (by change Integrable (fun x => u x * ((T : ℂ) * w x * E x)); rw [heq]; exact hAE.const_mul _)
    hDE huE
  change (∫ x : ℝ, u x * ((T : ℂ) * w x * E x)) = _ at hI
  rw [heq, integral_const_mul] at hI
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  calc
    _ = (T : ℂ)⁻¹ * ((T : ℂ) * ∫ x : ℝ, A x * E x) := by field_simp
    _ = _ := by rw [hI]; ring

theorem d06_nonstationary_repeated_integration {A r E w : ℝ → ℂ} {T : ℝ}
    (hT : T ≠ 0) (hA : ContDiff ℝ ∞ A) (hs : tsupport A ⊆ Icc (1 : ℝ) 2)
    (hr : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ r x)
    (hE : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ E x)
    (hEd : ∀ x ∈ tsupport A, HasDerivAt E ((T : ℂ) * w x * E x) x)
    (hinv : ∀ x ∈ tsupport A, r x * w x = 1) (k : ℕ) :
    (∫ x : ℝ, A x * E x) =
      (-(T : ℂ)⁻¹) ^ k * ∫ x : ℝ, d06NonstationaryAmplitude A r k x * E x := by
  induction k with
  | zero => simp [d06NonstationaryAmplitude]
  | succ k hk =>
      rw [hk, d06_nonstationary_one_step hT
        (d06_nonstationary_amplitude_contDiff hA hr k)
        ((d06_nonstationary_amplitude_support A r k).trans hs)
        (fun x hx => hr x (d06_nonstationary_amplitude_support A r k hx))
        (fun x hx => hE x (d06_nonstationary_amplitude_support A r k hx))
        (fun x hx => hEd x (d06_nonstationary_amplitude_support A r k hx))
        (fun x hx => hinv x (d06_nonstationary_amplitude_support A r k hx))]
      simp only [pow_succ, d06NonstationaryAmplitude, mul_assoc]

theorem d06_nonstationary_repeated_integral_bound {A r E w : ℝ → ℂ} {T : ℝ}
    (hT : 0 < T) (hA : ContDiff ℝ ∞ A) (hs : tsupport A ⊆ Icc (1 : ℝ) 2)
    (hr : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ r x)
    (hE : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ E x)
    (hEd : ∀ x ∈ tsupport A, HasDerivAt E ((T : ℂ) * w x * E x) x)
    (hinv : ∀ x ∈ tsupport A, r x * w x = 1)
    (hEn : ∀ x ∈ tsupport A, ‖E x‖ = 1)
    {C B : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (hB : ∀ j, 0 ≤ B j)
    (hAd : ∀ j x, ‖iteratedDeriv j A x‖ ≤ C j)
    (hrd : ∀ j x, x ∈ tsupport A → ‖iteratedDeriv j r x‖ ≤ B j) (k : ℕ) :
    ‖∫ x : ℝ, A x * E x‖ ≤ d06NonstationaryBudget C B k 0 / T ^ k := by
  let Ak := d06NonstationaryAmplitude A r k
  let K := d06NonstationaryBudget C B k 0
  have hK : 0 ≤ K := d06_nonstationary_budget_nonneg hC hB k 0
  have hAk := d06_nonstationary_amplitude_contDiff hA hr k
  have hAkSupp := d06_nonstationary_amplitude_support A r k
  have hn (x : ℝ) : ‖Ak x * E x‖ ≤ K := by
    by_cases hx : x ∈ tsupport A
    · rw [norm_mul, hEn x hx, mul_one]
      exact d06_nonstationary_amplitude_derivative_bound hA hr hC hB hAd hrd k 0 x
    · have hz : Ak x = 0 :=
        Function.notMem_support.mp (fun hh => hx (hAkSupp (subset_tsupport _ hh)))
      simp only [hz, zero_mul, norm_zero]
      exact hK
  have hi : Integrable (fun x => Ak x * E x) :=
    d06_supported_product_integrable hAk (hAkSupp.trans hs)
      (fun x hx => hE x (hAkSupp hx))
  have he : (∫ x : ℝ, ‖Ak x * E x‖) =
      ∫ x : ℝ in Icc (1 : ℝ) 2, ‖Ak x * E x‖ := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Icc (1 : ℝ) 2
    · simp only [indicator_of_mem hx]
    · have hz : Ak x = 0 :=
        Function.notMem_support.mp (fun hh => hx (hs (hAkSupp (subset_tsupport _ hh))))
      simp only [indicator_of_notMem hx, hz, zero_mul, norm_zero]
  have hJ : ‖∫ x : ℝ, Ak x * E x‖ ≤ K := by
    apply (norm_integral_le_integral_norm _).trans
    rw [he]
    calc
      _ ≤ ∫ _x : ℝ in Icc (1 : ℝ) 2, K :=
        integral_mono hi.norm.integrableOn (integrableOn_const (measure_Icc_lt_top.ne)) hn
      _ = K := by norm_num [Real.volume_real_Icc]
  rw [d06_nonstationary_repeated_integration hT.ne' hA hs hr hE hEd hinv k,
    norm_mul, norm_pow, norm_neg, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hT]
  calc
    _ ≤ (T⁻¹) ^ k * K := mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = K / T ^ k := by rw [inv_pow]; ring

theorem d06_nonstationary_time_integral_bound {A r E w : ℝ → ℂ} {T : ℝ}
    (hT : 0 < T) (hA : ContDiff ℝ ∞ A) (hs : tsupport A ⊆ Icc (1 : ℝ) 2)
    (hr : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ r x)
    (hE : ∀ x ∈ tsupport A, ContDiffAt ℝ ∞ E x)
    (hEd : ∀ x ∈ tsupport A, HasDerivAt E ((T : ℂ) * w x * E x) x)
    (hinv : ∀ x ∈ tsupport A, r x * w x = 1)
    (hEn : ∀ x ∈ tsupport A, ‖E x‖ = 1)
    {C B : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (hB : ∀ j, 0 ≤ B j)
    (hAd : ∀ j x, ‖iteratedDeriv j A x‖ ≤ C j)
    (hrd : ∀ j x, x ∈ tsupport A → ‖iteratedDeriv j r x‖ ≤ B j) (k : ℕ) :
    ‖∫ t : ℝ, A (t / T) * E (t / T)‖ ≤
      d06NonstationaryBudget C B k 0 * T / T ^ k := by
  have hb := d06_nonstationary_repeated_integral_bound hT hA hs hr hE hEd hinv
    hEn hC hB hAd hrd k
  have he : (∫ t : ℝ, A (t / T) * E (t / T)) =
      (T : ℂ) * ∫ x : ℝ, A x * E x := by
    simpa only [abs_of_pos hT, Complex.real_smul] using
      (Measure.integral_comp_div (fun x => A x * E x) T)
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  exact (mul_le_mul_of_nonneg_left hb hT.le).trans_eq (by ring)

end
end Sechstmoment
