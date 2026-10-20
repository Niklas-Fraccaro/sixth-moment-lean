import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import SixthMoment.Analysis.Complex.CauchyBounds


namespace SixthMoment

open Filter Metric Asymptotics MeasureTheory
open scoped BigOperators

noncomputable section

def reciprocalSquareSum (s : ℂ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), (‖s + (j : ℂ)‖ ^ 2)⁻¹

theorem norm_add_ofReal_sq (s : ℂ) (x : ℝ) :
    ‖s + (x : ℂ)‖ ^ 2 = (s.re + x) ^ 2 + s.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
  ring

private theorem inverse_square_tail_le (m N : ℕ) (hm : 0 < m) :
    ∑ i ∈ Finset.range N, (1 / ((m + 1 + i : ℕ) : ℝ) ^ 2) ≤ 1 / (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  calc
    _ ≤ ∑ i ∈ Finset.range N,
        (1 / ((m + i : ℕ) : ℝ) - 1 / ((m + i + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      have hp : 0 < ((m + i : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + i)
      simp only [Nat.cast_add, Nat.cast_one]
      have hp' : 0 < (m : ℝ) + i := by exact_mod_cast (by omega : 0 < m + i)
      field_simp
      nlinarith
    _ = 1 / (m : ℝ) - 1 / ((m + N : ℕ) : ℝ) := by
      have h := Finset.sum_range_sub (fun i : ℕ => -(1 / ((m + i : ℕ) : ℝ))) N
      simpa only [neg_sub_neg, Nat.add_zero, Nat.add_assoc] using h
    _ ≤ _ := sub_le_self _ (by positivity)

theorem reciprocalSquareSum_range_le (s : ℂ) (N : ℕ)
    (hre : 0 ≤ s.re) (him : 1 ≤ |s.im|) :
    ∑ j ∈ Finset.range N, (‖s + (j : ℂ)‖ ^ 2)⁻¹ ≤ 4 / |s.im| := by
  let t : ℝ := |s.im|
  let m : ℕ := ⌊t⌋₊
  let f : ℕ → ℝ := fun j => (‖s + (j : ℂ)‖ ^ 2)⁻¹
  have ht : 1 ≤ t := him
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hm : 0 < m := Nat.floor_pos.mpr ht
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmle : (m : ℝ) ≤ t := Nat.floor_le ht0.le
  have htlt : t < (m : ℝ) + 1 := Nat.lt_floor_add_one t
  have hmone : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have ht2m : t ≤ 2 * (m : ℝ) := by linarith
  have hnear (j : ℕ) : f j ≤ 1 / t ^ 2 := by
    dsimp [f]
    rw [← one_div]
    apply one_div_le_one_div_of_le (sq_pos_of_pos ht0)
    have heq := norm_add_ofReal_sq s (j : ℝ)
    have ht2 : t ^ 2 = s.im ^ 2 := by dsimp [t]; exact sq_abs _
    simp only [Complex.ofReal_natCast] at heq
    rw [heq, ht2]
    exact le_add_of_nonneg_left (sq_nonneg _)
  have hfar (j : ℕ) (hj : 0 < j) : f j ≤ 1 / (j : ℝ) ^ 2 := by
    dsimp [f]
    rw [← one_div]
    apply one_div_le_one_div_of_le (sq_pos_of_pos (Nat.cast_pos.mpr hj))
    have heq := norm_add_ofReal_sq s (j : ℝ)
    simp only [Complex.ofReal_natCast] at heq
    rw [heq]
    nlinarith [sq_nonneg s.im, sq_nonneg s.re, mul_nonneg hre (Nat.cast_nonneg j)]
  calc
    ∑ j ∈ Finset.range N, f j ≤ ∑ j ∈ Finset.range (m + 1 + N), f j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (by omega))
      intro j _ _
      dsimp [f]
      positivity
    _ = (∑ j ∈ Finset.range (m + 1), f j) +
        ∑ i ∈ Finset.range N, f (m + 1 + i) := Finset.sum_range_add f (m + 1) N
    _ ≤ (m + 1 : ℝ) / t ^ 2 + 1 / (m : ℝ) := by
      apply add_le_add
      · calc
          _ ≤ ∑ _j ∈ Finset.range (m + 1), 1 / t ^ 2 := Finset.sum_le_sum (fun j _ => hnear j)
          _ = _ := by simp [div_eq_mul_inv]
      · exact (Finset.sum_le_sum (fun i _ => hfar (m + 1 + i) (by omega))).trans
          (inverse_square_tail_le m N hm)
    _ ≤ 2 / t + 2 / t := by
      apply add_le_add
      · apply (div_le_div_iff₀ (sq_pos_of_pos ht0) ht0).mpr
        have hsum : (m : ℝ) + 1 ≤ 2 * t := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hsum ht0.le]
      · exact (div_le_div_iff₀ hmR ht0).mpr (by nlinarith)
    _ = 4 / |s.im| := by dsimp [t]; ring

theorem reciprocalSquareSum_le (s : ℂ) (n : ℕ)
    (hre : 0 ≤ s.re) (him : 1 ≤ |s.im|) :
    reciprocalSquareSum s n ≤ 4 / |s.im| :=
  reciprocalSquareSum_range_le s (n + 1) hre him

theorem add_ofReal_ne_zero_of_im_ne_zero (s : ℂ) (x : ℝ) (him : s.im ≠ 0) :
    s + (x : ℂ) ≠ 0 := by
  intro h
  have h' := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] at h'
  exact him h'

theorem reciprocal_add_ofReal_continuous (s : ℂ) (him : s.im ≠ 0) :
    Continuous (fun x : ℝ => (s + (x : ℂ))⁻¹) := by
  apply Continuous.inv₀ (by fun_prop)
  exact fun x => add_ofReal_ne_zero_of_im_ne_zero s x him

theorem norm_add_ofReal_mono (s : ℂ) (hre : 0 ≤ s.re)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖s + (a : ℂ)‖ ≤ ‖s + (b : ℂ)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_add_ofReal_sq, norm_add_ofReal_sq]
  have hprod : 0 ≤ (b - a) * (2 * s.re + a + b) :=
    mul_nonneg (sub_nonneg.mpr hab) (by linarith)
  nlinarith

theorem reciprocal_unitInterval_point_error_le (s : ℂ) (j : ℕ)
    (hre : 0 ≤ s.re) (him : s.im ≠ 0) {x : ℝ}
    (hx : x ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1)) :
    ‖(s + (j : ℂ))⁻¹ - (s + (x : ℂ))⁻¹‖ ≤ (‖s + (j : ℂ)‖ ^ 2)⁻¹ := by
  have hjne : s + (j : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_natCast] using add_ofReal_ne_zero_of_im_ne_zero s (j : ℝ) him
  have hxne := add_ofReal_ne_zero_of_im_ne_zero s x him
  have hjpos : 0 < ‖s + (j : ℂ)‖ := norm_pos_iff.mpr hjne
  have hxpos : 0 < ‖s + (x : ℂ)‖ := norm_pos_iff.mpr hxne
  have hmono : ‖s + (j : ℂ)‖ ≤ ‖s + (x : ℂ)‖ := by
    simpa only [Complex.ofReal_natCast] using norm_add_ofReal_mono s hre (Nat.cast_nonneg j) hx.1
  have heq : (s + (j : ℂ))⁻¹ - (s + (x : ℂ))⁻¹ =
      ((x - (j : ℝ) : ℝ) : ℂ) / ((s + (j : ℂ)) * (s + (x : ℂ))) := by
    push_cast
    field_simp
    ring
  rw [heq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hx.1)]
  calc
    (x - (j : ℝ)) / (‖s + (j : ℂ)‖ * ‖s + (x : ℂ)‖) ≤
        1 / (‖s + (j : ℂ)‖ * ‖s + (x : ℂ)‖) :=
      div_le_div_of_nonneg_right (by linarith [hx.2]) (mul_pos hjpos hxpos).le
    _ ≤ 1 / (‖s + (j : ℂ)‖ * ‖s + (j : ℂ)‖) :=
      one_div_le_one_div_of_le (mul_pos hjpos hjpos)
        (mul_le_mul_of_nonneg_left hmono hjpos.le)
    _ = _ := by rw [pow_two, one_div]

theorem reciprocal_unitInterval_integral_error_le (s : ℂ) (j : ℕ)
    (hre : 0 ≤ s.re) (him : s.im ≠ 0) :
    ‖(s + (j : ℂ))⁻¹ - (∫ x in (j : ℝ)..((j + 1 : ℕ) : ℝ),
        (s + (x : ℂ))⁻¹)‖ ≤ (‖s + (j : ℂ)‖ ^ 2)⁻¹ := by
  have hi := (reciprocal_add_ofReal_continuous s him).intervalIntegrable (μ := volume)
    (j : ℝ) ((j + 1 : ℕ) : ℝ)
  have heq : (s + (j : ℂ))⁻¹ - (∫ x in (j : ℝ)..((j + 1 : ℕ) : ℝ),
      (s + (x : ℂ))⁻¹) =
      ∫ x in (j : ℝ)..((j + 1 : ℕ) : ℝ),
        ((s + (j : ℂ))⁻¹ - (s + (x : ℂ))⁻¹) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const]
    simp
  rw [heq]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (j : ℝ)) (b := ((j + 1 : ℕ) : ℝ))
    (C := (‖s + (j : ℂ)‖ ^ 2)⁻¹) (f := fun x : ℝ =>
      (s + (j : ℂ))⁻¹ - (s + (x : ℂ))⁻¹) (by
        intro x hx
        rw [Set.uIoc_of_le (by simp)] at hx
        apply reciprocal_unitInterval_point_error_le s j hre him
        simpa only [Nat.cast_add, Nat.cast_one] using Set.Ioc_subset_Icc_self hx)
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, abs_one, mul_one] using h

theorem reciprocalSum_integral_error_le (s : ℂ) (N : ℕ)
    (hre : 0 ≤ s.re) (him : 1 ≤ |s.im|) :
    ‖(∑ j ∈ Finset.range N, (s + (j : ℂ))⁻¹) -
      (∫ x in (0 : ℝ)..(N : ℝ), (s + (x : ℂ))⁻¹)‖ ≤ 4 / |s.im| := by
  have him0 : s.im ≠ 0 := by intro h; simp only [h, abs_zero] at him; linarith
  have hi := (reciprocal_add_ofReal_continuous s him0).intervalIntegrable (μ := volume)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ)) (n := N) (fun j _ => hi (j : ℝ) ((j + 1 : ℕ) : ℝ))
  simp only [Nat.cast_zero] at hsum
  rw [← hsum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        ‖(s + (j : ℂ))⁻¹ - (∫ x in (j : ℝ)..((j + 1 : ℕ) : ℝ),
          (s + (x : ℂ))⁻¹)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, (‖s + (j : ℂ)‖ ^ 2)⁻¹ :=
      Finset.sum_le_sum (fun j _ => reciprocal_unitInterval_integral_error_le s j hre him0)
    _ ≤ _ := reciprocalSquareSum_range_le s N hre him

theorem integral_reciprocal_eq_log_sub (s : ℂ) (N : ℕ) (him : s.im ≠ 0) :
    (∫ x in (0 : ℝ)..(N : ℝ), (s + (x : ℂ))⁻¹) =
      Complex.log (s + (N : ℂ)) - Complex.log s := by
  have hi := (reciprocal_add_ofReal_continuous s him).intervalIntegrable
    (μ := volume) (0 : ℝ) (N : ℝ)
  have hderiv (x : ℝ) : HasDerivAt (fun x : ℝ => Complex.log (s + (x : ℂ)))
      ((s + (x : ℂ))⁻¹) x := by
    have hlin : HasDerivAt (fun y : ℝ => s + (y : ℂ)) (1 : ℂ) x := by
      simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one] using
        Complex.ofRealCLM.hasDerivAt.const_add s
    have hslit : s + (x : ℂ) ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inr (by simpa only [Complex.add_im,
        Complex.ofReal_im, add_zero] using him))
    simpa only [one_div] using hlin.clog_real hslit
  simpa only [Complex.ofReal_zero, add_zero, Complex.ofReal_natCast] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hi

theorem reciprocalSum_log_error_le (s : ℂ) (N : ℕ)
    (hre : 0 ≤ s.re) (him : 1 ≤ |s.im|) :
    ‖(∑ j ∈ Finset.range N, (s + (j : ℂ))⁻¹) -
      (Complex.log (s + (N : ℂ)) - Complex.log s)‖ ≤ 4 / |s.im| := by
  have him0 : s.im ≠ 0 := by intro h; simp only [h, abs_zero] at him; linarith
  rw [← integral_reciprocal_eq_log_sub s N him0]
  exact reciprocalSum_integral_error_le s N hre him

theorem reciprocalSquareSum_range_cone_six_le (s : ℂ) (N : ℕ)
    (hre : -|s.im| ≤ s.re) (him : 1 ≤ |s.im|) :
    ∑ j ∈ Finset.range N, (‖s + (j : ℂ)‖ ^ 2)⁻¹ ≤ 6 / |s.im| := by
  let t : ℝ := |s.im|
  let m : ℕ := ⌈t⌉₊
  let f : ℕ → ℝ := fun j => (‖s + (j : ℂ)‖ ^ 2)⁻¹
  have ht : 1 ≤ t := him
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hmge : t ≤ (m : ℝ) := Nat.le_ceil t
  have hmle : (m : ℝ) ≤ t + 1 := by
    calc
      (m : ℝ) ≤ (⌊t⌋₊ : ℝ) + 1 := by exact_mod_cast Nat.ceil_le_floor_add_one t
      _ ≤ t + 1 := by linarith [Nat.floor_le ht0.le]
  have hm2 : (m : ℝ) ≤ 2 * t := by linarith
  have hnear (j : ℕ) : f j ≤ 1 / t ^ 2 := by
    dsimp [f]
    rw [← one_div]
    apply one_div_le_one_div_of_le (sq_pos_of_pos ht0)
    have hnorm : t ≤ ‖s + (j : ℂ)‖ := by
      simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
        Complex.abs_im_le_norm (s + (j : ℂ))
    exact (sq_le_sq₀ ht0.le (norm_nonneg _)).mpr hnorm
  have hshiftre : 0 ≤ (s + (m : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    dsimp [t] at hmge
    linarith
  have htail : (∑ i ∈ Finset.range N, f (m + i)) ≤ 4 / t := by
    have h := reciprocalSquareSum_range_le (s + (m : ℂ)) N hshiftre
      (by simpa only [Complex.add_im, Complex.natCast_im, add_zero] using him)
    have heq : (∑ i ∈ Finset.range N, f (m + i)) =
        ∑ i ∈ Finset.range N, (‖(s + (m : ℂ)) + (i : ℂ)‖ ^ 2)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp [f]
      rw [Nat.cast_add, add_assoc]
    rw [heq]
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using h
  calc
    ∑ j ∈ Finset.range N, f j ≤ ∑ j ∈ Finset.range (m + N), f j := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      intro j _ _
      dsimp [f]
      positivity
    _ = (∑ j ∈ Finset.range m, f j) + ∑ i ∈ Finset.range N, f (m + i) :=
      Finset.sum_range_add f m N
    _ ≤ (m : ℝ) / t ^ 2 + 4 / t := by
      apply add_le_add _ htail
      calc
        _ ≤ ∑ _j ∈ Finset.range m, 1 / t ^ 2 := Finset.sum_le_sum (fun j _ => hnear j)
        _ = _ := by simp [div_eq_mul_inv]
    _ ≤ 2 / t + 4 / t := by
      apply add_le_add _ le_rfl
      apply (div_le_div_iff₀ (sq_pos_of_pos ht0) ht0).mpr
      nlinarith [mul_le_mul_of_nonneg_right hm2 ht0.le]
    _ = 6 / |s.im| := by dsimp [t]; ring

theorem reciprocalSquareSum_cone_six_le (s : ℂ) (n : ℕ)
    (hre : -|s.im| ≤ s.re) (him : 1 ≤ |s.im|) :
    reciprocalSquareSum s n ≤ 6 / |s.im| :=
  reciprocalSquareSum_range_cone_six_le s (n + 1) hre him

theorem reciprocalSquareSum_cone_le (s : ℂ) (n : ℕ)
    (hre : -|s.im| ≤ s.re) (him : 2 ≤ |s.im|) :
    reciprocalSquareSum s n ≤ 16 / |s.im| := by
  exact (reciprocalSquareSum_cone_six_le s n hre (by linarith)).trans
    (div_le_div_of_nonneg_right (by norm_num) (abs_nonneg _))

theorem reciprocal_unitInterval_point_error_le_of_large_im (s : ℂ) (j : ℕ)
    (him : 2 ≤ |s.im|) {x : ℝ}
    (hx : x ∈ Set.Icc (j : ℝ) ((j : ℝ) + 1)) :
    ‖(s + (j : ℂ))⁻¹ - (s + (x : ℂ))⁻¹‖ ≤
      2 * (‖s + (j : ℂ)‖ ^ 2)⁻¹ := by
  have him0 : s.im ≠ 0 := by intro h; simp only [h, abs_zero] at him; linarith
  have hjne : s + (j : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_natCast] using add_ofReal_ne_zero_of_im_ne_zero s (j : ℝ) him0
  have hxne := add_ofReal_ne_zero_of_im_ne_zero s x him0
  have hjpos : 0 < ‖s + (j : ℂ)‖ := norm_pos_iff.mpr hjne
  have hxpos : 0 < ‖s + (x : ℂ)‖ := norm_pos_iff.mpr hxne
  have hxnorm : 2 ≤ ‖s + (x : ℂ)‖ := by
    have h := Complex.abs_im_le_norm (s + (x : ℂ))
    simp only [Complex.add_im, Complex.ofReal_im, add_zero] at h
    exact him.trans h
  have hdiff : ‖(s + (j : ℂ)) - (s + (x : ℂ))‖ ≤ 1 := by
    have heq : (s + (j : ℂ)) - (s + (x : ℂ)) = (((j : ℝ) - x : ℝ) : ℂ) := by
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith [hx.1])]
    linarith [hx.2]
  have hratio : ‖s + (j : ℂ)‖ ≤ 2 * ‖s + (x : ℂ)‖ := by
    have h := (norm_sub_norm_le (s + (j : ℂ)) (s + (x : ℂ))).trans hdiff
    linarith
  have heq : (s + (j : ℂ))⁻¹ - (s + (x : ℂ))⁻¹ =
      ((x - (j : ℝ) : ℝ) : ℂ) / ((s + (j : ℂ)) * (s + (x : ℂ))) := by
    push_cast
    field_simp
    ring
  rw [heq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hx.1)]
  calc
    (x - (j : ℝ)) / (‖s + (j : ℂ)‖ * ‖s + (x : ℂ)‖) ≤
        1 / (‖s + (j : ℂ)‖ * ‖s + (x : ℂ)‖) :=
      div_le_div_of_nonneg_right (by linarith [hx.2]) (mul_pos hjpos hxpos).le
    _ ≤ 2 / (‖s + (j : ℂ)‖ ^ 2) := by
      apply (div_le_div_iff₀ (mul_pos hjpos hxpos) (sq_pos_of_pos hjpos)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hratio hjpos.le]
    _ = _ := by rw [div_eq_mul_inv]

theorem reciprocal_unitInterval_integral_error_le_of_large_im (s : ℂ) (j : ℕ)
    (him : 2 ≤ |s.im|) :
    ‖(s + (j : ℂ))⁻¹ - (∫ x in (j : ℝ)..((j + 1 : ℕ) : ℝ),
        (s + (x : ℂ))⁻¹)‖ ≤ 2 * (‖s + (j : ℂ)‖ ^ 2)⁻¹ := by
  have him0 : s.im ≠ 0 := by intro h; simp only [h, abs_zero] at him; linarith
  have hi := (reciprocal_add_ofReal_continuous s him0).intervalIntegrable (μ := volume)
    (j : ℝ) ((j + 1 : ℕ) : ℝ)
  have heq : (s + (j : ℂ))⁻¹ - (∫ x in (j : ℝ)..((j + 1 : ℕ) : ℝ),
      (s + (x : ℂ))⁻¹) =
      ∫ x in (j : ℝ)..((j + 1 : ℕ) : ℝ),
        ((s + (j : ℂ))⁻¹ - (s + (x : ℂ))⁻¹) := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hi,
      intervalIntegral.integral_const]
    simp
  rw [heq]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (j : ℝ)) (b := ((j + 1 : ℕ) : ℝ))
    (C := 2 * (‖s + (j : ℂ)‖ ^ 2)⁻¹) (f := fun x : ℝ =>
      (s + (j : ℂ))⁻¹ - (s + (x : ℂ))⁻¹) (by
        intro x hx
        rw [Set.uIoc_of_le (by simp)] at hx
        apply reciprocal_unitInterval_point_error_le_of_large_im s j him
        simpa only [Nat.cast_add, Nat.cast_one] using Set.Ioc_subset_Icc_self hx)
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, abs_one, mul_one] using h

theorem reciprocalSum_integral_error_cone_twelve_le (s : ℂ) (N : ℕ)
    (hre : -|s.im| ≤ s.re) (him : 2 ≤ |s.im|) :
    ‖(∑ j ∈ Finset.range N, (s + (j : ℂ))⁻¹) -
      (∫ x in (0 : ℝ)..(N : ℝ), (s + (x : ℂ))⁻¹)‖ ≤ 12 / |s.im| := by
  have him0 : s.im ≠ 0 := by intro h; simp only [h, abs_zero] at him; linarith
  have hi := (reciprocal_add_ofReal_continuous s him0).intervalIntegrable (μ := volume)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun j : ℕ => (j : ℝ)) (n := N) (fun j _ => hi (j : ℝ) ((j + 1 : ℕ) : ℝ))
  simp only [Nat.cast_zero] at hsum
  rw [← hsum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ Finset.range N,
        ‖(s + (j : ℂ))⁻¹ - (∫ x in (j : ℝ)..((j + 1 : ℕ) : ℝ),
          (s + (x : ℂ))⁻¹)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, 2 * (‖s + (j : ℂ)‖ ^ 2)⁻¹ :=
      Finset.sum_le_sum (fun j _ => reciprocal_unitInterval_integral_error_le_of_large_im s j him)
    _ = 2 * ∑ j ∈ Finset.range N, (‖s + (j : ℂ)‖ ^ 2)⁻¹ := (Finset.mul_sum _ _ _).symm
    _ ≤ 2 * (6 / |s.im|) := mul_le_mul_of_nonneg_left
      (reciprocalSquareSum_range_cone_six_le s N hre (by linarith)) (by norm_num)
    _ = _ := by ring

theorem reciprocalSum_log_error_cone_twelve_le (s : ℂ) (N : ℕ)
    (hre : -|s.im| ≤ s.re) (him : 2 ≤ |s.im|) :
    ‖(∑ j ∈ Finset.range N, (s + (j : ℂ))⁻¹) -
      (Complex.log (s + (N : ℂ)) - Complex.log s)‖ ≤ 12 / |s.im| := by
  have him0 : s.im ≠ 0 := by intro h; simp only [h, abs_zero] at him; linarith
  rw [← integral_reciprocal_eq_log_sub s N him0]
  exact reciprocalSum_integral_error_cone_twelve_le s N hre him

theorem reciprocalSum_log_error_cone_le (s : ℂ) (N : ℕ)
    (hre : -|s.im| ≤ s.re) (him : 2 ≤ |s.im|) :
    ‖(∑ j ∈ Finset.range N, (s + (j : ℂ))⁻¹) -
      (Complex.log (s + (N : ℂ)) - Complex.log s)‖ ≤ 32 / |s.im| := by
  exact (reciprocalSum_log_error_cone_twelve_le s N hre him).trans
    (div_le_div_of_nonneg_right (by norm_num) (abs_nonneg _))

end

end SixthMoment
