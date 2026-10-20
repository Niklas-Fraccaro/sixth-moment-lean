import Sechstmoment.Denominator.Balanced.ActualGaussianTruncation
import Sechstmoment.Denominator.Balanced.GaussianMainTermIdentity
import Sechstmoment.Denominator.Balanced.GaussianPhysicalTimeMean

namespace Sechstmoment
open Complex Real Source MeasureTheory Set
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d02_positive_shifted_dirichlet_phase_split {x : ℝ} (hx : 0 < x)
    (α : ℂ) (t : ℝ) :
    1 / (x : ℂ) ^ ((1 / 2 : ℂ) + α + (t : ℂ) * I) =
      (x : ℂ) ^ (-(1 / 2 : ℂ) - α) *
        Complex.exp (((-t * Real.log x : ℝ) : ℂ) * I) := by
  have hn : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hx.ne'
  calc
    _ = Complex.exp (-((Real.log x : ℂ) * ((1 / 2 : ℂ) + α + (t : ℂ) * I))) := by
      rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log hx.le,
        one_div, ← Complex.exp_neg]
    _ = Complex.exp ((Real.log x : ℂ) * (-(1 / 2 : ℂ) - α)) *
        Complex.exp (((-t * Real.log x : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = _ := by rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log hx.le]

theorem d02ActualGaussianSummand_eq_pairTerm (α : Fin 2 → ℂ) (t : ℝ) (n : ℕ × ℕ) :
    d02ActualGaussianSummand (criticalLinePoint t + α 0)
      (1 - criticalLinePoint t + α 1) t n = d02GaussianPairTerm α t n := by
  have hm : 0 < (n.1 + 1 : ℝ) := by positivity
  have hn : 0 < (n.2 + 1 : ℝ) := by positivity
  have hs : criticalLinePoint t + α 0 = (1 / 2 : ℂ) + α 0 + (t : ℂ) * I := by
    unfold criticalLinePoint
    ring
  have hr : 1 - criticalLinePoint t + α 1 = (1 / 2 : ℂ) + α 1 + ((-t : ℝ) : ℂ) * I := by
    unfold criticalLinePoint
    push_cast
    ring
  have hl : 1 / (n.1 + 1 : ℂ) ^ (criticalLinePoint t + α 0) =
      (n.1 + 1 : ℂ) ^ (-(1 / 2 : ℂ) - α 0) *
        Complex.exp (((-t * Real.log (n.1 + 1 : ℝ) : ℝ) : ℂ) * I) := by
    rw [hs, show (n.1 + 1 : ℂ) = ((n.1 + 1 : ℝ) : ℂ) by push_cast; rfl]
    exact d02_positive_shifted_dirichlet_phase_split hm _ t
  have hr' : 1 / (n.2 + 1 : ℂ) ^ (1 - criticalLinePoint t + α 1) =
      (n.2 + 1 : ℂ) ^ (-(1 / 2 : ℂ) - α 1) *
        Complex.exp (((t * Real.log (n.2 + 1 : ℝ) : ℝ) : ℂ) * I) := by
    rw [hr, show (n.2 + 1 : ℂ) = ((n.2 + 1 : ℝ) : ℂ) by push_cast; rfl]
    simpa only [neg_neg] using d02_positive_shifted_dirichlet_phase_split hn (α 1) (-t)
  have he : Complex.exp (((-t * Real.log (n.1 + 1 : ℝ) : ℝ) : ℂ) * I) *
      Complex.exp (((t * Real.log (n.2 + 1 : ℝ) : ℝ) : ℂ) * I) =
      Complex.exp (((-t * Real.log ((n.1 + 1 : ℝ) / (n.2 + 1 : ℝ)) : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add, Real.log_div hm.ne' hn.ne']
    congr 1
    push_cast
    ring
  unfold d02ActualGaussianSummand d02ActualPairCoefficient d02GaussianPairTerm d02PairDirichletCoefficient
  rw [← one_div_mul_one_div, hl, hr', ← he]
  ring

theorem d02ActualGaussianSeries_eq_pairSeries (α : Fin 2 → ℂ) (t : ℝ) :
    (∑' n : ℕ × ℕ, d02ActualGaussianSummand (criticalLinePoint t + α 0)
      (1 - criticalLinePoint t + α 1) t n) = ∑' n : ℕ × ℕ, d02GaussianPairTerm α t n :=
  tsum_congr (d02ActualGaussianSummand_eq_pairTerm α t)

theorem d02_actual_four_profiles_gaussian_finite_identity {T : ℝ} (hT : 1 < T)
    (t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (α : Fin 2 → ℂ) (P : Finset (ℕ × ℕ)) :
    d02BalancedAmplifier T t ρ *
      (∑ p ∈ P, d02ActualGaussianSummand (criticalLinePoint t + α 0)
        (1 - criticalLinePoint t + α 1) t p) =
      ∑ q ∈ d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊) P, d02SixRawGaussianTerm T t ρ α q := by
  have hs : (∑ p ∈ P, d02ActualGaussianSummand (criticalLinePoint t + α 0)
      (1 - criticalLinePoint t + α 1) t p) = ∑ p ∈ P, d02GaussianPairTerm α t p :=
    Finset.sum_congr rfl (fun p _ => d02ActualGaussianSummand_eq_pairTerm α t p)
  rw [hs]
  exact d02_four_profiles_gaussian_pair_finite_identity hT t a ρ hcap α P

theorem d02_actual_four_profiles_gaussian_full_identity {T : ℝ} (hT : 1 < T)
    {t : ℝ} (ht : 0 < t) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (α : Fin 2 → ℂ) :
    d02BalancedAmplifier T t ρ *
      (∑' p : ℕ × ℕ, d02ActualGaussianSummand (criticalLinePoint t + α 0)
        (1 - criticalLinePoint t + α 1) t p) =
      ∑' q : Fin 6 → ℕ, d02SixRawGaussianTerm T t ρ α q := by
  rw [d02ActualGaussianSeries_eq_pairSeries]
  exact d02_four_profiles_gaussian_pair_full_identity hT ht a ρ hcap α

theorem d02_actual_gaussian_full_diagonal_time_identity {T : ℝ} (hT : 1 < T)
    {Φ : ℝ → ℂ} (hΦs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (α : Fin 2 → ℂ) (τ : ℂ) :
    Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ * d02BalancedAmplifier T t ρ *
      (∑' p : ℕ × ℕ, d02ActualGaussianSummand (criticalLinePoint t + α 0)
        (1 - criticalLinePoint t + α 1) t p) =
      (Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ) *
        ((∑' q : {q : Fin 6 → ℕ // d02SixIsDiagonal q},
          d02SixRawGaussianTerm T t ρ α q.val) +
         (∑' q : {q : Fin 6 → ℕ // ¬d02SixIsDiagonal q},
          d02SixRawGaussianTerm T t ρ α q.val)) := by
  rw [d02ActualGaussianSeries_eq_pairSeries]
  exact d02SixMain_full_diagonal_add_offDiagonal_time_identity hT hΦs t a ρ hcap α τ

theorem d02_actual_four_profiles_gaussian_finite_time_integral {T : ℝ} (hT : 1 < T)
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ ⊆ Icc (1 : ℝ) 2)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0)
    (σ : Fin 2 → ℂ) (τ : ℂ) (P : Finset (ℕ × ℕ)) :
    (∫ t : ℝ, Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ * d02BalancedAmplifier T t ρ *
      ∑ p ∈ P, d02ActualGaussianSummand
        (criticalLinePoint t + σ 0 / (Real.log T : ℂ))
        (1 - criticalLinePoint t + σ 1 / (Real.log T : ℂ)) t p) =
      ∑ q ∈ d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊) P,
        (d02SixProfileMultiplier T ρ q *
          d02ShiftedSqrtCoefficient T (d02SixZetaShifts σ) q) *
          a03ProfileTimeFourier (d02SixGaussianTimeProfile Φ T τ q) T
            (d02SixGaussianFrequency q) := by
  have he : (fun t : ℝ => Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ * d02BalancedAmplifier T t ρ *
      ∑ p ∈ P, d02ActualGaussianSummand
        (criticalLinePoint t + σ 0 / (Real.log T : ℂ))
        (1 - criticalLinePoint t + σ 1 / (Real.log T : ℂ)) t p) =
      fun t : ℝ => Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ *
        ∑ q ∈ d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊) P,
          d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q := by
    funext t
    have hp := d02_actual_four_profiles_gaussian_finite_identity hT t a ρ hcap
      (fun j => σ j / (Real.log T : ℂ)) P
    calc
      _ = (Φ (t / T) * ((t / T : ℝ) : ℂ) ^ τ) *
          (d02BalancedAmplifier T t ρ *
            ∑ p ∈ P, d02ActualGaussianSummand
              (criticalLinePoint t + σ 0 / (Real.log T : ℂ))
              (1 - criticalLinePoint t + σ 1 / (Real.log T : ℂ)) t p) := by ring
      _ = _ := by rw [hp]
  rw [he]
  exact d02SixRawGaussianTerm_finite_time_integral (zero_lt_one.trans hT) hΦ hs ρ σ τ _

theorem d02ActualPairCut_fromD01_iff {T : ℝ} (hT : 1 < T)
    (δ : ℝ) (x : DiagonalSixIndices) :
    ((d02DiagonalFromD01 x).val 4, (d02DiagonalFromD01 x).val 5) ∈
        d02ActualPairCut (T ^ (1 + δ)) ↔
      d02LogCutCoordinate (d01LogPoint (Real.log T) x) ≤ 1 + δ := by
  have hTp : 0 < T := zero_lt_one.trans hT
  have hL : 0 < Real.log T := Real.log_pos hT
  have hm : (d02DiagonalFromD01 x).val 4 + 1 = d01LeftIndices x 0 := by
    simpa [d02DiagonalFromD01] using
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01LeftIndices_pos x 0))
  have hn : (d02DiagonalFromD01 x).val 5 + 1 = d01RightIndices x 0 := by
    simpa [d02DiagonalFromD01] using
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01RightIndices_pos x 0))
  rw [d02ActualPairCut_mem_iff (Real.rpow_pos_of_pos hTp _),
    d02GaussianTruncatedLogRegion_logPoint_iff hL]
  have he : d02PositivePairProduct
      ((d02DiagonalFromD01 x).val 4, (d02DiagonalFromD01 x).val 5) =
      (d01LeftIndices x 0 : ℝ) * (d01RightIndices x 0 : ℝ) := by
    unfold d02PositivePairProduct
    rw [show ((d02DiagonalFromD01 x).val 4 : ℝ) + 1 = (d01LeftIndices x 0 : ℝ) by
      exact_mod_cast hm,
      show ((d02DiagonalFromD01 x).val 5 : ℝ) + 1 = (d01RightIndices x 0 : ℝ) by
      exact_mod_cast hn]
  rw [he, Real.rpow_def_of_pos hTp]

theorem d02_actual_finite_gaussian_diagonal_measure_identity {T : ℝ} (hT : 1 < T)
    (δ t : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (σ : Fin 2 → ℂ) :
    (∑ q ∈ (d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊)
        (d02ActualPairCut (T ^ (1 + δ)))).filter d02SixIsDiagonal,
      d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q) /
        (Real.log T : ℂ) ^ 9 =
      ∫ y, d01ComplexLaplaceWeight (![σ 0, 0, 0], ![σ 1, 0, 0]) y *
        d02GaussianTruncatedFourProfile δ (fun j x => (ρ j x : ℂ)) y *
        (d02GaussianV0 (2 * Real.pi * Real.exp
          (Real.log T * d02LogCutCoordinate y) / t) : ℂ)
        ∂d01DiagonalMeasure (Real.log T) := by
  classical
  have hL : 0 < Real.log T := Real.log_pos hT
  let M : D01LogSpace → ℂ := fun y => if d02LogCutCoordinate y ≤ 1 + δ then 1 else 0
  have hf : (fun y : D01LogSpace =>
      d01ComplexLaplaceWeight (![σ 0, 0, 0], ![σ 1, 0, 0]) y *
        d02GaussianTruncatedFourProfile δ (fun j x => (ρ j x : ℂ)) y *
        (d02GaussianV0 (2 * Real.pi * Real.exp
          (Real.log T * d02LogCutCoordinate y) / t) : ℂ)) =
      fun y : D01LogSpace => M y * d02GaussianDiagonalTest (Real.log T) t
        (fun j x => (ρ j x : ℂ))
        (d01ComplexLaplaceWeight (![σ 0, 0, 0], ![σ 1, 0, 0])) y := by
    funext y
    by_cases h : d02LogCutCoordinate y ≤ 1 + δ
    · have h' : y.1 0 + y.2 0 ≤ 1 + δ := h
      simp [M, d02GaussianTruncatedFourProfile, d02GaussianDiagonalTest,
        d02FourProfileProduct, d02LogCutCoordinate, h']
    · have h' : ¬(y.1 0 + y.2 0 ≤ 1 + δ) := h
      simp [M, d02GaussianTruncatedFourProfile, d02GaussianDiagonalTest,
        d02LogCutCoordinate, h']
  rw [d02SixRawGaussianTerm_finite_diagonal_tsum_identity hT t a ρ hcap]
  rw [d02_positive_diagonal_tsum_reindex (fun q : Fin 6 → ℕ =>
      if (q 4, q 5) ∈ d02ActualPairCut (T ^ (1 + δ)) then
        d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q else 0), hf,
    d02GaussianDiagonal_masked_shifted_measure_identity hL]
  apply congrArg (fun z : ℂ => z / (Real.log T : ℂ) ^ 9)
  apply tsum_congr
  intro x
  have hshift₁ : (fun i : Fin 3 => (![σ 0, 0, 0] i) / (Real.log T : ℂ)) =
      ![σ 0 / (Real.log T : ℂ), 0, 0] := by funext i; fin_cases i <;> simp
  have hshift₂ : (fun i : Fin 3 => (![σ 1, 0, 0] i) / (Real.log T : ℂ)) =
      ![σ 1 / (Real.log T : ℂ), 0, 0] := by funext i; fin_cases i <;> simp
  rw [hshift₁, hshift₂]
  have hcut := d02ActualPairCut_fromD01_iff hT δ x
  by_cases h : d02LogCutCoordinate (d01LogPoint (Real.log T) x) ≤ 1 + δ
  · rw [ite_eq_left (hcut.2 h), d02SixRawGaussianTerm_fromD01_identity]
    simp [M, h]
  · rw [ite_eq_right (hcut.not.2 h)]
    simp [M, h]

theorem d02_actual_finite_gaussian_diagonal_time_mean_identity {T : ℝ} (hT : 1 < T)
    (δ : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x, a j < x → ρ j x = 0) (σ : Fin 2 → ℂ) (Φ : ℝ → ℝ) :
    (∫ t : ℝ, (Φ (t / T) : ℂ) *
      ∑ q ∈ (d02SixMainDomain (fun j => ⌊T ^ (a j)⌋₊)
        (d02ActualPairCut (T ^ (1 + δ)))).filter d02SixIsDiagonal,
        d02SixRawGaussianTerm T t ρ (fun j => σ j / (Real.log T : ℂ)) q) /
          ((T : ℂ) * (Real.log T : ℂ) ^ 9) =
      d02GaussianTruncatedDiagonalPhysicalHeightMean δ T (fun j x => (ρ j x : ℂ))
        (![σ 0, 0, 0], ![σ 1, 0, 0]) Φ := by
  unfold d02GaussianTruncatedDiagonalPhysicalHeightMean
  rw [show (T : ℂ) * (Real.log T : ℂ) ^ 9 =
      (Real.log T : ℂ) ^ 9 * (T : ℂ) by ring,
    div_mul_eq_div_div, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mul_div_assoc, d02_actual_finite_gaussian_diagonal_measure_identity hT δ t a ρ hcap]

end
end Sechstmoment
