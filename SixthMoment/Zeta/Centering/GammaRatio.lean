import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.FieldSimp
import SixthMoment.Zeta.Centering.Exact
import SixthMoment.Zeta.Gamma.ReciprocalSums


namespace SixthMoment
open Complex Filter
open scoped BigOperators Topology
noncomputable section

def gammaRatioEuler (s u : ℂ) (n : ℕ) : ℂ :=
  (n : ℂ)^u * ∏ j ∈ Finset.range (n+1), (s+j)/(s+u+j)

private theorem shifted_nat_ne_zero {s : ℂ} (hs : 0 < s.re) (j : ℕ) :
    s+j ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  simp only [add_re, natCast_re, zero_re] at hr
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem gammaRatioEuler_eq_GammaSeq_ratio {s u : ℂ}
    (hs : 0 < s.re) (hsu : 0 < (s+u).re) {n : ℕ} (hn : n ≠ 0) :
    gammaRatioEuler s u n = GammaSeq (s+u) n / GammaSeq s n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hf : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hp : (∏ j ∈ Finset.range (n+1), (s+j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => shifted_nat_ne_zero hs j)
  have hp' : (∏ j ∈ Finset.range (n+1), (s+u+j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => shifted_nat_ne_zero hsu j)
  unfold gammaRatioEuler GammaSeq
  rw [Complex.cpow_add _ _ hn', Finset.prod_div_distrib]
  have hnp : (n : ℂ)^s ≠ 0 := by simp [hn']
  field_simp

theorem gammaRatioEuler_tendsto {s u : ℂ} (hs : 0 < s.re) (hsu : 0 < (s+u).re) :
    Tendsto (gammaRatioEuler s u) atTop (𝓝 (Gamma (s+u)/Gamma s)) := by
  apply Tendsto.congr' _
    ((GammaSeq_tendsto_Gamma (s+u)).div (GammaSeq_tendsto_Gamma s)
      (Gamma_ne_zero_of_re_pos hs))
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (gammaRatioEuler_eq_GammaSeq_ratio hs hsu hn).symm

theorem gammaRatioEuler_exp {s u : ℂ} (hs : 0 < s.re) (hsu : 0 < (s+u).re)
    {n : ℕ} (hn : n ≠ 0) :
    gammaRatioEuler s u n = Complex.exp
      (Complex.log (n : ℂ)*u -
        ∑ j ∈ Finset.range (n+1), Complex.log (1+u/(s+j))) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hterm (j : ℕ) : 1+u/(s+j) ≠ 0 := by
    have ha := shifted_nat_ne_zero hs j
    have hb := shifted_nat_ne_zero hsu j
    have he : 1+u/(s+j) = (s+u+j)/(s+j) := by field_simp; ring
    rw [he]
    exact div_ne_zero hb ha
  rw [Complex.exp_sub, Complex.exp_sum, ← Complex.cpow_def_of_ne_zero hn']
  simp_rw [Complex.exp_log (hterm _)]
  unfold gammaRatioEuler
  simp only [div_eq_mul_inv]
  rw [← Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have ha := shifted_nat_ne_zero hs j
  have hb := shifted_nat_ne_zero hsu j
  have hb' : s+j+u ≠ 0 := by convert hb using 1; ring
  field_simp
  ring

theorem norm_log_one_add_sub_self_le_sq {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    ‖Complex.log (1+w)-w‖ ≤ ‖w‖^2 := by
  have hsmall : ‖w‖ < 1 := by linarith
  apply (Complex.norm_log_one_add_sub_self_le hsmall).trans
  have hi : (1-‖w‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1-‖w‖)]
    linarith
  have hn : 0 ≤ ‖w‖^2 := sq_nonneg _
  have hm := mul_le_mul_of_nonneg_left hi hn
  linarith

def gammaRatioTaylorError (s u : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (n+1), (Complex.log (1+u/(s+j))-u/(s+j))

theorem gammaRatioEuler_exp_reciprocal {s u : ℂ}
    (hs : 0 < s.re) (hsu : 0 < (s+u).re) {n : ℕ} (hn : n ≠ 0) :
    gammaRatioEuler s u n = Complex.exp
      (u*(Complex.log (n : ℂ)-∑ j ∈ Finset.range (n+1), (s+j)⁻¹) -
        gammaRatioTaylorError s u n) := by
  rw [gammaRatioEuler_exp hs hsu hn]
  congr 1
  unfold gammaRatioTaylorError
  simp only [Finset.sum_sub_distrib, div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

theorem gammaRatioTaylorError_norm_le (s u : ℂ) (n : ℕ)
    (hsmall : ∀ j ∈ Finset.range (n+1), ‖u/(s+j)‖ ≤ 1/2) :
    ‖gammaRatioTaylorError s u n‖ ≤
      ‖u‖^2 * ∑ j ∈ Finset.range (n+1), (‖s+j‖^2)⁻¹ := by
  unfold gammaRatioTaylorError
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ‖u/(s+j)‖^2 := by
      apply Finset.sum_le_sum
      intro j hj
      exact norm_log_one_add_sub_self_le_sq (hsmall j hj)
    _ = _ := by
      simp only [div_eq_mul_inv, norm_mul, norm_inv, mul_pow, inv_pow, Finset.mul_sum]

def gammaRatioLogTail (s : ℂ) (n : ℕ) : ℂ :=
  Complex.log (n : ℂ)-Complex.log (s+n+1)

def gammaRatioReciprocalError (s : ℂ) (n : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (n+1), (s+j)⁻¹) -
    (Complex.log (s+n+1)-Complex.log s)

theorem gammaRatioEuler_normalized_exp {s u : ℂ} (hs : 0 < s.re)
    (hsu : 0 < (s+u).re) {n : ℕ} (hn : n ≠ 0) :
    gammaRatioEuler s u n / s^u = Complex.exp
      (u*(gammaRatioLogTail s n-gammaRatioReciprocalError s n)-
        gammaRatioTaylorError s u n) := by
  have hs' : s ≠ 0 := by
    intro h
    simp only [h, zero_re] at hs
    exact (lt_irrefl 0) hs
  rw [gammaRatioEuler_exp_reciprocal hs hsu hn,
    Complex.cpow_def_of_ne_zero hs', ← Complex.exp_sub]
  congr 1
  unfold gammaRatioLogTail gammaRatioReciprocalError
  ring

theorem gammaRatioEuler_normalized_tendsto {s u : ℂ}
    (hs : 0 < s.re) (hsu : 0 < (s+u).re) :
    Tendsto (fun n => gammaRatioEuler s u n / s^u) atTop
      (𝓝 ((Gamma (s+u)/Gamma s)/s^u)) :=
  (gammaRatioEuler_tendsto hs hsu).div_const _

private theorem gammaRatioLogTail_eq {s : ℂ} (hs : 0 < s.re)
    {n : ℕ} (hn : n ≠ 0) :
    gammaRatioLogTail s n = -Complex.log ((s+n+1)/(n : ℂ)) := by
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hz : s+n+1 ≠ 0 := by
    intro hz
    have hr := congrArg Complex.re hz
    simp only [add_re, natCast_re, one_re, zero_re] at hr
    linarith
  have he : (s+n+1)/(n : ℂ) = ((1/(n : ℝ) : ℝ) : ℂ)*(s+n+1) := by
    push_cast
    ring
  rw [he, Complex.log_ofReal_mul (one_div_pos.mpr hnreal) hz]
  unfold gammaRatioLogTail
  have hnlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnreal.le).symm
  rw [hnlog, Real.log_div one_ne_zero hnreal.ne', Real.log_one]
  push_cast
  ring

theorem gammaRatioLogTail_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (gammaRatioLogTail s) atTop (𝓝 0) := by
  have hratio : Tendsto (fun n : ℕ => (s+n+1)/(n : ℂ)) atTop (𝓝 1) := by
    have hbase := (tendsto_const_nhds (x := (1 : ℂ))).add (tendsto_const_div_atTop_nhds_zero_nat (s+1))
    apply Tendsto.congr' _ (show Tendsto (fun n : ℕ => 1+(s+1)/(n : ℂ))
      atTop (𝓝 1) by simpa using hbase)
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
    ring
  have hlog : Tendsto (fun n : ℕ => -Complex.log ((s+n+1)/(n : ℂ))) atTop (𝓝 0) := by
    simpa using (hratio.clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).neg
  apply Tendsto.congr' _ hlog
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (gammaRatioLogTail_eq hs hn).symm

theorem gammaRatio_log_factor_small (s u : ℂ) (him : 0 < |s.im|)
    (hu : 2*‖u‖ ≤ |s.im|) (j : ℕ) : ‖u/(s+j)‖ ≤ 1/2 := by
  have hnorm : |s.im| ≤ ‖s+j‖ := by
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
      Complex.abs_im_le_norm (s+(j : ℂ))
  have hnormpos : 0 < ‖s+j‖ := him.trans_le hnorm
  rw [norm_div, div_le_iff₀ hnormpos]
  linarith

theorem gammaRatioTaylorError_vertical_le (s u : ℂ) (n : ℕ)
    (hre : 0 ≤ s.re) (him : 1 ≤ |s.im|) (hu : 2*‖u‖ ≤ |s.im|) :
    ‖gammaRatioTaylorError s u n‖ ≤ 4*‖u‖^2/|s.im| := by
  have hsmall (j : ℕ) (_hj : j ∈ Finset.range (n+1)) :=
    gammaRatio_log_factor_small s u (zero_lt_one.trans_le him) hu j
  apply (gammaRatioTaylorError_norm_le s u n hsmall).trans
  have hsum := reciprocalSquareSum_le s n hre him
  unfold reciprocalSquareSum at hsum
  calc
    _ ≤ ‖u‖^2*(4/|s.im|) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by ring

private theorem shifted_nat_ne_zero_of_im_ne {s : ℂ} (hs : s.im ≠ 0) (j : ℕ) :
    s+j ≠ 0 := by
  intro hz
  apply hs
  simpa only [Complex.add_im, Complex.natCast_im, add_zero, Complex.zero_im] using
    congrArg Complex.im hz

private theorem gamma_ne_zero_of_im_ne {s : ℂ} (hs : s.im ≠ 0) : Gamma s ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  apply hs
  simpa only [Complex.neg_im, Complex.natCast_im, neg_zero] using congrArg Complex.im hn

theorem gammaRatioEuler_eq_GammaSeq_ratio_of_im_ne {s u : ℂ}
    (hs : s.im ≠ 0) (hsu : (s+u).im ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    gammaRatioEuler s u n = GammaSeq (s+u) n / GammaSeq s n := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hf : (Nat.factorial n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hp : (∏ j ∈ Finset.range (n+1), (s+j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => shifted_nat_ne_zero_of_im_ne hs j)
  have hp' : (∏ j ∈ Finset.range (n+1), (s+u+j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => shifted_nat_ne_zero_of_im_ne hsu j)
  unfold gammaRatioEuler GammaSeq
  rw [Complex.cpow_add _ _ hn', Finset.prod_div_distrib]
  have hnp : (n : ℂ)^s ≠ 0 := by simp [hn']
  field_simp

theorem gammaRatioEuler_tendsto_of_im_ne {s u : ℂ}
    (hs : s.im ≠ 0) (hsu : (s+u).im ≠ 0) :
    Tendsto (gammaRatioEuler s u) atTop (𝓝 (Gamma (s+u)/Gamma s)) := by
  apply Tendsto.congr' _
    ((GammaSeq_tendsto_Gamma (s+u)).div (GammaSeq_tendsto_Gamma s)
      (gamma_ne_zero_of_im_ne hs))
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (gammaRatioEuler_eq_GammaSeq_ratio_of_im_ne hs hsu hn).symm

theorem gammaRatioEuler_exp_of_im_ne {s u : ℂ} (hs : s.im ≠ 0)
    (hsu : (s+u).im ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    gammaRatioEuler s u n = Complex.exp
      (Complex.log (n : ℂ)*u -
        ∑ j ∈ Finset.range (n+1), Complex.log (1+u/(s+j))) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hterm (j : ℕ) : 1+u/(s+j) ≠ 0 := by
    have ha := shifted_nat_ne_zero_of_im_ne hs j
    have hb := shifted_nat_ne_zero_of_im_ne hsu j
    have he : 1+u/(s+j) = (s+u+j)/(s+j) := by field_simp; ring
    rw [he]
    exact div_ne_zero hb ha
  rw [Complex.exp_sub, Complex.exp_sum, ← Complex.cpow_def_of_ne_zero hn']
  simp_rw [Complex.exp_log (hterm _)]
  unfold gammaRatioEuler
  simp only [div_eq_mul_inv]
  rw [← Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have ha := shifted_nat_ne_zero_of_im_ne hs j
  have hb := shifted_nat_ne_zero_of_im_ne hsu j
  have hb' : s+j+u ≠ 0 := by convert hb using 1; ring
  field_simp
  ring

theorem gammaRatioEuler_normalized_exp_of_im_ne {s u : ℂ}
    (hs : s.im ≠ 0) (hsu : (s+u).im ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    gammaRatioEuler s u n / s^u = Complex.exp
      (u*(gammaRatioLogTail s n-gammaRatioReciprocalError s n)-
        gammaRatioTaylorError s u n) := by
  have hs' : s ≠ 0 := by intro h; exact hs (by simp [h])
  rw [gammaRatioEuler_exp_of_im_ne hs hsu hn,
    Complex.cpow_def_of_ne_zero hs', ← Complex.exp_sub]
  congr 1
  unfold gammaRatioLogTail gammaRatioReciprocalError gammaRatioTaylorError
  simp only [Finset.sum_sub_distrib, div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

theorem gammaRatioEuler_normalized_tendsto_of_im_ne {s u : ℂ}
    (hs : s.im ≠ 0) (hsu : (s+u).im ≠ 0) :
    Tendsto (fun n => gammaRatioEuler s u n / s^u) atTop
      (𝓝 ((Gamma (s+u)/Gamma s)/s^u)) :=
  (gammaRatioEuler_tendsto_of_im_ne hs hsu).div_const _

private theorem gammaRatioLogTail_eq_of_im_ne {s : ℂ} (hs : s.im ≠ 0)
    {n : ℕ} (hn : n ≠ 0) :
    gammaRatioLogTail s n = -Complex.log ((s+n+1)/(n : ℂ)) := by
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hz : s+n+1 ≠ 0 := by
    intro hz
    apply hs
    simpa only [Complex.add_im, Complex.natCast_im, Complex.one_im, add_zero,
      Complex.zero_im] using congrArg Complex.im hz
  have he : (s+n+1)/(n : ℂ) = ((1/(n : ℝ) : ℝ) : ℂ)*(s+n+1) := by
    push_cast
    ring
  rw [he, Complex.log_ofReal_mul (one_div_pos.mpr hnreal) hz]
  unfold gammaRatioLogTail
  have hnlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_natCast] using (Complex.ofReal_log hnreal.le).symm
  rw [hnlog, Real.log_div one_ne_zero hnreal.ne', Real.log_one]
  push_cast
  ring

theorem gammaRatioLogTail_tendsto_of_im_ne {s : ℂ} (hs : s.im ≠ 0) :
    Tendsto (gammaRatioLogTail s) atTop (𝓝 0) := by
  have hratio : Tendsto (fun n : ℕ => (s+n+1)/(n : ℂ)) atTop (𝓝 1) := by
    have hbase := (tendsto_const_nhds (x := (1 : ℂ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (s+1))
    apply Tendsto.congr' _ (show Tendsto (fun n : ℕ => 1+(s+1)/(n : ℂ))
      atTop (𝓝 1) by simpa using hbase)
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
    ring
  have hlog : Tendsto (fun n : ℕ => -Complex.log ((s+n+1)/(n : ℂ))) atTop (𝓝 0) := by
    simpa using (hratio.clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).neg
  apply Tendsto.congr' _ hlog
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (gammaRatioLogTail_eq_of_im_ne hs hn).symm

theorem gammaRatio_normalized_error_of_finite_errors {s u : ℂ}
    (hs : s.im ≠ 0) (hsu : (s+u).im ≠ 0) {E : ℝ} (hE : E < 1)
    (herr : ∀ n : ℕ, ‖u‖*‖gammaRatioReciprocalError s n‖ +
      ‖gammaRatioTaylorError s u n‖ ≤ E) :
    ‖(Gamma (s+u)/Gamma s)/s^u - 1‖ ≤ 2*E := by
  have htail : Tendsto (fun n => ‖u‖*‖gammaRatioLogTail s n‖) atTop (𝓝 0) := by
    simpa using (gammaRatioLogTail_tendsto_of_im_ne hs).norm.const_mul ‖u‖
  have hexp (n : ℕ) :
      ‖u*(gammaRatioLogTail s n-gammaRatioReciprocalError s n)-
        gammaRatioTaylorError s u n‖ ≤ ‖u‖*‖gammaRatioLogTail s n‖+E := by
    calc
      _ ≤ ‖u‖*‖gammaRatioLogTail s n-gammaRatioReciprocalError s n‖ +
          ‖gammaRatioTaylorError s u n‖ := by
        simpa only [norm_mul] using norm_sub_le
          (u*(gammaRatioLogTail s n-gammaRatioReciprocalError s n))
          (gammaRatioTaylorError s u n)
      _ ≤ ‖u‖*(‖gammaRatioLogTail s n‖+‖gammaRatioReciprocalError s n‖) +
          ‖gammaRatioTaylorError s u n‖ := by
        exact add_le_add (mul_le_mul_of_nonneg_left
          (norm_sub_le (gammaRatioLogTail s n) (gammaRatioReciprocalError s n)) (norm_nonneg u))
          (le_refl ‖gammaRatioTaylorError s u n‖)
      _ ≤ _ := by linarith [herr n]
  have hbound : ∀ᶠ n : ℕ in atTop,
      ‖gammaRatioEuler s u n/s^u-1‖ ≤ 2*(‖u‖*‖gammaRatioLogTail s n‖+E) := by
    filter_upwards [eventually_ne_atTop 0, htail.eventually_lt_const (by linarith : 0 < 1-E)]
      with n hn hsmall
    rw [gammaRatioEuler_normalized_exp_of_im_ne hs hsu hn]
    apply (Complex.norm_exp_sub_one_le (by linarith [hexp n])).trans
    exact mul_le_mul_of_nonneg_left (hexp n) (by norm_num)
  have hlim : Tendsto (fun n => ‖gammaRatioEuler s u n/s^u-1‖) atTop
      (𝓝 ‖(Gamma (s+u)/Gamma s)/s^u-1‖) :=
    ((gammaRatioEuler_normalized_tendsto_of_im_ne hs hsu).sub_const 1).norm
  have hlim' : Tendsto (fun n => 2*(‖u‖*‖gammaRatioLogTail s n‖+E)) atTop
      (𝓝 (2*E)) := by simpa using (htail.add_const E).const_mul 2
  exact le_of_tendsto_of_tendsto hlim hlim' hbound

theorem gammaRatio_normalized_error_vertical (s u : ℂ)
    (hre : 0 ≤ s.re) (him : 1 ≤ |s.im|)
    (hu : 8*(‖u‖+‖u‖^2) < |s.im|) :
    ‖(Gamma (s+u)/Gamma s)/s^u-1‖ ≤ 8*(‖u‖+‖u‖^2)/|s.im| := by
  have ht : 0 < |s.im| := zero_lt_one.trans_le him
  have hs : s.im ≠ 0 := by intro h; simp only [h, abs_zero] at ht; linarith
  have hsmall : 2*‖u‖ ≤ |s.im| := by nlinarith [sq_nonneg ‖u‖, norm_nonneg u]
  have hsu : (s+u).im ≠ 0 := by
    intro h
    have hi : s.im = -u.im := by simp only [Complex.add_im] at h; linarith
    have hnorm := Complex.abs_im_le_norm u
    rw [hi, abs_neg] at hu
    nlinarith [sq_nonneg ‖u‖, norm_nonneg u]
  have hE : 4*(‖u‖+‖u‖^2)/|s.im| < 1 :=
    (div_lt_iff₀ ht).mpr (by nlinarith [norm_nonneg u, sq_nonneg ‖u‖])
  have herr (n : ℕ) : ‖u‖*‖gammaRatioReciprocalError s n‖ +
      ‖gammaRatioTaylorError s u n‖ ≤ 4*(‖u‖+‖u‖^2)/|s.im| := by
    have hr := reciprocalSum_log_error_le s (n+1) hre him
    have hr' : ‖gammaRatioReciprocalError s n‖ ≤ 4/|s.im| := by
      simpa only [gammaRatioReciprocalError, Nat.cast_add, Nat.cast_one, add_assoc] using hr
    have hq := gammaRatioTaylorError_vertical_le s u n hre him hsmall
    calc
      _ ≤ ‖u‖*(4/|s.im|)+4*‖u‖^2/|s.im| :=
        add_le_add (mul_le_mul_of_nonneg_left hr' (norm_nonneg _)) hq
      _ = _ := by ring
  calc
    _ ≤ 2*(4*(‖u‖+‖u‖^2)/|s.im|) :=
      gammaRatio_normalized_error_of_finite_errors hs hsu hE herr
    _ = _ := by ring

theorem gammaRatioTaylorError_cone_le (s u : ℂ) (n : ℕ)
    (hre : -|s.im| ≤ s.re) (him : 1 ≤ |s.im|) (hu : 2*‖u‖ ≤ |s.im|) :
    ‖gammaRatioTaylorError s u n‖ ≤ 6*‖u‖^2/|s.im| := by
  have hsmall (j : ℕ) (_hj : j ∈ Finset.range (n+1)) :=
    gammaRatio_log_factor_small s u (zero_lt_one.trans_le him) hu j
  apply (gammaRatioTaylorError_norm_le s u n hsmall).trans
  have hsum := reciprocalSquareSum_cone_six_le s n hre him
  unfold reciprocalSquareSum at hsum
  calc
    _ ≤ ‖u‖^2*(6/|s.im|) := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by ring

theorem gammaRatio_normalized_error_cone (s u : ℂ)
    (hre : -|s.im| ≤ s.re) (him : 2 ≤ |s.im|)
    (hu : 24*(‖u‖+‖u‖^2) < |s.im|) :
    ‖(Gamma (s+u)/Gamma s)/s^u-1‖ ≤ 24*(‖u‖+‖u‖^2)/|s.im| := by
  have ht : 0 < |s.im| := by linarith
  have hs : s.im ≠ 0 := by intro h; simp only [h, abs_zero] at ht; linarith
  have hsmall : 2*‖u‖ ≤ |s.im| := by nlinarith [sq_nonneg ‖u‖, norm_nonneg u]
  have hsu : (s+u).im ≠ 0 := by
    intro h
    have hi : s.im = -u.im := by simp only [Complex.add_im] at h; linarith
    have hnorm := Complex.abs_im_le_norm u
    rw [hi, abs_neg] at hu
    nlinarith [sq_nonneg ‖u‖, norm_nonneg u]
  have hE : 12*(‖u‖+‖u‖^2)/|s.im| < 1 :=
    (div_lt_iff₀ ht).mpr (by nlinarith [norm_nonneg u, sq_nonneg ‖u‖])
  have herr (n : ℕ) : ‖u‖*‖gammaRatioReciprocalError s n‖ +
      ‖gammaRatioTaylorError s u n‖ ≤ 12*(‖u‖+‖u‖^2)/|s.im| := by
    have hr := reciprocalSum_log_error_cone_twelve_le s (n+1) hre him
    have hr' : ‖gammaRatioReciprocalError s n‖ ≤ 12/|s.im| := by
      simpa only [gammaRatioReciprocalError, Nat.cast_add, Nat.cast_one, add_assoc] using hr
    have hq := gammaRatioTaylorError_cone_le s u n hre (by linarith) hsmall
    calc
      _ ≤ ‖u‖*(12/|s.im|)+6*‖u‖^2/|s.im| :=
        add_le_add (mul_le_mul_of_nonneg_left hr' (norm_nonneg _)) hq
      _ ≤ _ := by
        have hnon : 0 ≤ 6*‖u‖^2/|s.im| := by positivity
        have he : ‖u‖*(12/|s.im|)+6*‖u‖^2/|s.im| + 6*‖u‖^2/|s.im| =
            12*(‖u‖+‖u‖^2)/|s.im| := by ring
        linarith
  calc
    _ ≤ 2*(12*(‖u‖+‖u‖^2)/|s.im|) :=
      gammaRatio_normalized_error_of_finite_errors hs hsu hE herr
    _ = _ := by ring

end
end SixthMoment
