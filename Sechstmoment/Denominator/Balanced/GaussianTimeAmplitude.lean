import Sechstmoment.Analysis.Complex.PositivePowers
import Sechstmoment.Analysis.Fourier.ProfileProduct
import Sechstmoment.Analysis.Gaussian.Mellin
import Sechstmoment.Numerator.U.Separation.Frequency.Composition
import Sechstmoment.Numerator.U.ZeroModes.RatioGlobalLogDerivatives

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1500000

theorem d02_logarithmic_time_uniform_derivative_bounds {F : ℝ → ℂ}
    (hF : ContDiff ℝ ∞ F) (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    (hFd : ∀ n u, ‖iteratedDeriv n F u‖ ≤ C n) :
    ∃ D : ℕ → ℝ, (∀ n, 0 ≤ D n) ∧ ∀ c : ℝ, ∀ x ∈ Icc (1 : ℝ) 2,
      ContDiffAt ℝ ∞ (fun y : ℝ => F (c - Real.log y)) x ∧
      ∀ n, ‖iteratedDeriv n (fun y : ℝ => F (c - Real.log y)) x‖ ≤ D n := by
  let g : ℝ → ℝ := fun y => -Real.log y
  have hg : ContDiffOn ℝ ∞ g (Ioi 0) := by
    intro y hy
    exact (Real.contDiffAt_log.2 (ne_of_gt hy)).neg.contDiffWithinAt
  have hbound (i : ℕ) : ∃ b : ℝ, ∀ x ∈ Icc (1 : ℝ) 2,
      ‖iteratedFDerivWithin ℝ i g (Ioi 0) x‖ ≤ b := by
    apply isCompact_Icc.exists_bound_of_continuousOn
    exact (hg.continuousOn_iteratedFDerivWithin (by simp) (uniqueDiffOn_Ioi (0 : ℝ))).mono
      (fun x hx => zero_lt_one.trans_le hx.1)
  choose b hb using hbound
  let B : ℕ → ℝ := fun i => max (b i) 0
  have hB (i : ℕ) : 0 ≤ B i := le_max_right _ _
  let E : ℕ → ℝ := fun n => 1 + ∑ i ∈ Finset.range (n + 1), B i
  have hE (n : ℕ) : 1 ≤ E n := by
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hB i))
  let K : ℕ → ℝ := fun n => ∑ i ∈ Finset.range (n + 1), C i
  have hK (n : ℕ) : 0 ≤ K n := Finset.sum_nonneg (fun i _ => hC i)
  let D : ℕ → ℝ := fun n => (n.factorial : ℝ) * K n * (E n) ^ n
  refine ⟨D, fun n => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK n))
    (pow_nonneg (zero_le_one.trans (hE n)) n), ?_⟩
  intro c x hx
  have hxp : 0 < x := zero_lt_one.trans_le hx.1
  have hA : ContDiffAt ℝ ∞ (fun y : ℝ => F (c - Real.log y)) x :=
    hF.contDiffAt.comp x (contDiffAt_const.sub (Real.contDiffAt_log.2 hxp.ne'))
  refine ⟨hA, ?_⟩
  intro n
  let Fc : ℝ → ℂ := fun u => F (c + u)
  have hFc : ContDiff ℝ ∞ Fc := hF.comp (contDiff_const.add contDiff_id)
  have hout (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i Fc univ (g x)‖ ≤ K n := by
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    dsimp only [Fc]
    rw [iteratedDeriv_comp_const_add]
    exact (hFd i _).trans (Finset.single_le_sum (fun j _ => hC j)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
  have hin (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i g (Ioi 0) x‖ ≤ (E n) ^ i := by
    have hb' : ‖iteratedFDerivWithin ℝ i g (Ioi 0) x‖ ≤ B i :=
      (hb i x hx).trans (le_max_left _ _)
    have hbi : B i ≤ E n := by
      have hh := Finset.single_le_sum (fun j _ => hB j)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hin))
      dsimp [E]
      linarith
    exact (hb'.trans hbi).trans (le_self_pow₀ (hE n) (by omega))
  have hh := norm_iteratedFDerivWithin_comp_le hFc.contDiffOn hg (by simp)
    uniqueDiffOn_univ (uniqueDiffOn_Ioi (0 : ℝ)) (mapsTo_univ _ _) hxp hout hin
  have he : Fc ∘ g = fun y : ℝ => F (c - Real.log y) := by
    funext y
    dsimp [Fc, g]
    rw [sub_eq_add_neg]
  rw [he, norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ioi (0 : ℝ)) (hA.of_le (by simp)) hxp] at hh
  exact hh

theorem d02GaussianMellin_eq_ratioLogDerivative (u : ℝ) :
    d02GaussianMellin u =
      a03ZeroModeRatioLogDerivative (a03ZeroModeRatioWeight (0 : MomentShifts)) 0 u := by
  unfold d02GaussianMellin d02GaussianMellinIntegrand a03ZeroModeRatioLogDerivative
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  let z : ℂ := 1 + (v : ℂ) * I
  have hG : a03ZeroModeRatioWeight (0 : MomentShifts) z = Complex.exp (z ^ 2) := by
    simp [a03ZeroModeRatioWeight, a03ZeroModeRatioRoot]
  change Complex.exp (z ^ 2 - (u : ℂ) * z) / z =
    (-z) ^ 0 * (a03ZeroModeRatioWeight (0 : MomentShifts) z / z) *
      Complex.exp (-z * (u : ℂ))
  rw [hG, pow_zero, one_mul,
    show z ^ 2 - (u : ℂ) * z = z ^ 2 + (-z * (u : ℂ)) by ring, Complex.exp_add]
  ring

theorem d02GaussianMellin_contDiff : ContDiff ℝ ∞ d02GaussianMellin := by
  have he : d02GaussianMellin =
      a03ZeroModeRatioLogDerivative (a03ZeroModeRatioWeight (0 : MomentShifts)) 0 :=
    funext d02GaussianMellin_eq_ratioLogDerivative
  rw [he]
  exact a03ZeroModeRatioLogDerivative_contDiff _ _ (a03ZeroModeRatioWeight_admissible _)

theorem d02GaussianMellin_global_derivative_bounds :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ n u, ‖iteratedDeriv n d02GaussianMellin u‖ ≤ C n := by
  let C : ℕ → ℝ := fun n => 1 + (gaussianTailConstant (n + 4) / (2 * Real.pi)) *
    a03ZeroModeRatioGaussianConstant (0 : MomentShifts) 1
  refine ⟨C, fun n => by
    have hgauss := gaussianTailConstant_nonneg (n + 4)
    have hratio := a03ZeroModeRatioGaussianConstant_nonneg (0 : MomentShifts) 1
    dsimp [C]
    positivity, ?_⟩
  intro n u
  have he : d02GaussianMellin =
      a03ZeroModeRatioLogDerivative (a03ZeroModeRatioWeight (0 : MomentShifts)) 0 :=
    funext d02GaussianMellin_eq_ratioLogDerivative
  rw [he, a03ZeroModeRatioLogDerivative_iteratedDeriv _ _ (a03ZeroModeRatioWeight_admissible _)]
  exact a03ZeroModeRatioLogDerivative_global_bound _ n u

def d02GaussianTimeAmplitude (X y : ℝ) : ℂ := d02GaussianMellin (Real.log X - Real.log y)

theorem d02GaussianTimeAmplitude_eq_weight {X y : ℝ} (hX : 0 < X) (hy : 0 < y) :
    d02GaussianTimeAmplitude X y = (d02GaussianV0 (X / y) : ℂ) := by
  rw [d02GaussianTimeAmplitude, d02GaussianMellin_eq_tail]
  unfold d02GaussianV0
  rw [Real.log_div hX.ne' hy.ne']

theorem d02GaussianProfile_eq_physical {Φ : ℝ → ℂ}
    (hs : tsupport Φ ⊆ Icc (1 : ℝ) 2) {X : ℝ} (hX : 0 < X) :
    a03ProfileProduct Φ (d02GaussianTimeAmplitude X) =
      fun y : ℝ => Φ y * (d02GaussianV0 (X / y) : ℂ) := by
  funext y
  by_cases hy : Φ y = 0
  · simp [a03ProfileProduct, hy]
  · have hpos : 0 < y := zero_lt_one.trans_le (hs (subset_tsupport _ hy)).1
    unfold a03ProfileProduct
    rw [d02GaussianTimeAmplitude_eq_weight hX hpos]

theorem d02GaussianTimeAmplitude_uniform_derivative_bounds :
    ∃ D : ℕ → ℝ, (∀ n, 0 ≤ D n) ∧ ∀ X : ℝ, ∀ x ∈ Icc (1 : ℝ) 2,
      ContDiffAt ℝ ∞ (d02GaussianTimeAmplitude X) x ∧
      ∀ n, ‖iteratedDeriv n (d02GaussianTimeAmplitude X) x‖ ≤ D n := by
  obtain ⟨C, hC, hd⟩ := d02GaussianMellin_global_derivative_bounds
  obtain ⟨D, hD, hb⟩ := d02_logarithmic_time_uniform_derivative_bounds d02GaussianMellin_contDiff C hC hd
  exact ⟨D, hD, fun X x hx => hb (Real.log X) x hx⟩

theorem d02GaussianProfile_uniform_derivative_bounds {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ ⊆ Icc (1 : ℝ) 2) :
    ∃ D : ℕ → ℝ, (∀ n, 0 ≤ D n) ∧ ∀ X : ℝ,
      ContDiff ℝ ∞ (a03ProfileProduct Φ (d02GaussianTimeAmplitude X)) ∧
      tsupport (a03ProfileProduct Φ (d02GaussianTimeAmplitude X)) ⊆ Icc (1 : ℝ) 2 ∧
      ∀ n x, ‖iteratedDeriv n (a03ProfileProduct Φ (d02GaussianTimeAmplitude X)) x‖ ≤ D n := by
  have hcompact : HasCompactSupport Φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  obtain ⟨C, hC, hCd⟩ := a03_profile_derivative_bounds hcompact hΦ
  obtain ⟨B, hB, hBd⟩ := d02GaussianTimeAmplitude_uniform_derivative_bounds
  let D := a03ProfileProductDerivativeBudget C B
  have hD (n : ℕ) : 0 ≤ D n := by
    unfold D a03ProfileProductDerivativeBudget
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hB (n - i)))
  refine ⟨D, hD, ?_⟩
  intro X
  have hA (x : ℝ) (hx : x ∈ Icc (1 : ℝ) 2) :
      ContDiffAt ℝ ∞ (d02GaussianTimeAmplitude X) x := (hBd X x hx).1
  refine ⟨a03_profile_product_contDiff hΦ (fun x hx => hA x (hs hx)),
    (a03_profile_product_tsupport _ _).trans hs, ?_⟩
  intro n x
  simpa only [mul_one] using a03_profile_product_derivative_bound hΦ hs hA hC hB hCd
    zero_le_one (fun j y hy => by simpa using (hBd X y hy).2 j) n x

theorem d02GaussianShiftedProfile_uniform_derivative_bounds {Φ : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ D : ℕ → ℝ, (∀ n, 0 ≤ D n) ∧ ∀ X : ℝ, ∀ q : ℂ, ‖q‖ ≤ R →
      ContDiff ℝ ∞ (a03ProfileProduct (a03ProfileProduct Φ (d02GaussianTimeAmplitude X))
        (fun y : ℝ => (y : ℂ) ^ q)) ∧
      tsupport (a03ProfileProduct (a03ProfileProduct Φ (d02GaussianTimeAmplitude X))
        (fun y : ℝ => (y : ℂ) ^ q)) ⊆ Icc (1 : ℝ) 2 ∧
      ∀ n x, ‖iteratedDeriv n
        (a03ProfileProduct (a03ProfileProduct Φ (d02GaussianTimeAmplitude X))
          (fun y : ℝ => (y : ℂ) ^ q)) x‖ ≤ D n := by
  obtain ⟨C, hC, hCd⟩ := d02GaussianProfile_uniform_derivative_bounds hΦ hs
  let B : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ n * (1 + R) ^ n * 2 ^ R
  have hB (n : ℕ) : 0 ≤ B n := by dsimp [B]; positivity
  let D := a03ProfileProductDerivativeBudget C B
  have hD (n : ℕ) : 0 ≤ D n := by
    unfold D a03ProfileProductDerivativeBudget
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hB (n - i)))
  refine ⟨D, hD, ?_⟩
  intro X q hq
  have hA (x : ℝ) (hx : x ∈ Icc (1 : ℝ) 2) :
      ContDiffAt ℝ ∞ (fun y : ℝ => (y : ℂ) ^ q) x :=
    positive_cpow_contDiffAt q (zero_lt_one.trans_le hx.1)
  have hAd (j : ℕ) (x : ℝ) (hx : x ∈ Icc (1 : ℝ) 2) :
      ‖iteratedDeriv j (fun y : ℝ => (y : ℂ) ^ q) x‖ ≤ B j * 1 := by
    have hxp : 0 < x := zero_lt_one.trans_le hx.1
    have hqr : q.re ≤ R := (Complex.re_le_norm q).trans hq
    have hp : x ^ (q.re - (j : ℝ)) ≤ 2 ^ R :=
      (Real.rpow_le_rpow_of_exponent_le hx.1 (by linarith [Nat.cast_nonneg (α := ℝ) j])).trans
        (Real.rpow_le_rpow hxp.le hx.2 hR)
    rw [positive_cpow_iteratedDeriv j q hxp, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hxp, Complex.sub_re, Complex.natCast_re]
    have hpow : (1 + ‖q‖) ^ j ≤ (1 + R) ^ j :=
      pow_le_pow_left₀ (by positivity) (by linarith) j
    have hf := (mellinFallingCoefficient_norm_le j q).trans
      (mul_le_mul_of_nonneg_left hpow (by positivity))
    calc
      _ ≤ (((j : ℝ) + 1) ^ j * (1 + R) ^ j) * 2 ^ R :=
        mul_le_mul hf hp (Real.rpow_nonneg hxp.le _) (by positivity)
      _ = _ := by dsimp [B]; ring
  have hfirst := hCd X
  refine ⟨a03_profile_product_contDiff hfirst.1 (fun x hx => hA x (hfirst.2.1 hx)),
    (a03_profile_product_tsupport _ _).trans hfirst.2.1, ?_⟩
  intro n x
  simpa only [mul_one] using a03_profile_product_derivative_bound hfirst.1 hfirst.2.1 hA hC hB
    hfirst.2.2 zero_le_one hAd n x

end
end Sechstmoment
