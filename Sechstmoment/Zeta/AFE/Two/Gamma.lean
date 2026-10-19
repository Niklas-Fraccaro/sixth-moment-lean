import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.GCongr
import Sechstmoment.Analysis.Gaussian.Tails
import Sechstmoment.Zeta.AFE.Four.GammaComparison
import Sechstmoment.Zeta.Gamma.PositiveStrip

/-!
# D02: the actual two-Gamma quotient and its normalized error

The shifted second-moment quotient uses one upper and one lower Gamma
argument. The principal phases cancel exactly. Its quantitative error is
proved from the Euler-product ratio estimate, with no AFE or moment source
assumption.
-/
namespace Sechstmoment.Source
open Complex Filter MeasureTheory Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

abbrev SecondMomentShifts := Fin 2 → ℂ

def secondSourceZetaPoints (t : ℝ) : SecondMomentShifts :=
  ![criticalLinePoint t, 1-criticalLinePoint t]

def secondGammaQuotient (t : ℝ) (α : SecondMomentShifts) (z : ℂ) : ℂ :=
  ∏ j : Fin 2, Gamma ((secondSourceZetaPoints t j+α j+z)/2) /
    Gamma ((secondSourceZetaPoints t j+α j)/2)

def secondGammaBase (t : ℝ) (α : SecondMomentShifts) (j : Fin 2) : ℂ :=
  (secondSourceZetaPoints t j+α j)/2

def secondGammaPhaseCenter : Fin 2 → ℂ := ![I,-I]

def secondGammaPhaseLogError (t : ℝ) (α : SecondMomentShifts) : ℂ :=
  ∑ j : Fin 2, (Complex.log (secondGammaBase t α j)-
    Complex.log (t/2 : ℂ)-Complex.log (secondGammaPhaseCenter j))

def secondGammaMainPhase (t : ℝ) (α : SecondMomentShifts) (z : ℂ) : ℂ :=
  (∏ j : Fin 2, (secondGammaBase t α j)^(z/2))/(t/2 : ℂ)^z

@[simp] theorem secondGammaPhaseCenter_norm (j : Fin 2) :
    ‖secondGammaPhaseCenter j‖ = 1 := by
  fin_cases j <;> simp [secondGammaPhaseCenter]

theorem secondGammaBase_scaled_sub_center {t : ℝ} (ht : t ≠ 0)
    (α : SecondMomentShifts) (j : Fin 2) :
    secondGammaBase t α j/(t/2 : ℂ)-secondGammaPhaseCenter j =
      ((1/2 : ℂ)+α j)/(t : ℂ) := by
  have htc : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  fin_cases j <;>
    simp [secondGammaBase, secondSourceZetaPoints, secondGammaPhaseCenter,
      criticalLinePoint] <;> field_simp <;> ring


private theorem secondGammaBase_scaled_norm_le {t A : ℝ}
    (hA : 0 ≤ A) (ht : 4*(A+1) ≤ t) (α : SecondMomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) (j : Fin 2) :
    ‖secondGammaBase t α j/(t/2 : ℂ)-secondGammaPhaseCenter j‖ ≤ (1/2+A)/t := by
  have htpos : 0 < t := by linarith
  rw [secondGammaBase_scaled_sub_center htpos.ne' α j, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  apply div_le_div_of_nonneg_right _ htpos.le
  calc
    ‖(1/2 : ℂ)+α j‖ ≤ ‖(1/2 : ℂ)‖+‖α j‖ := norm_add_le _ _
    _ ≤ 1/2+A := by norm_num; linarith [hα j]

private theorem secondGammaBase_scaled_ne_zero {t A : ℝ}
    (hA : 0 ≤ A) (ht : 4*(A+1) ≤ t) (α : SecondMomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) (j : Fin 2) :
    secondGammaBase t α j/(t/2 : ℂ) ≠ 0 := by
  have htpos : 0 < t := by linarith
  have hd := secondGammaBase_scaled_norm_le hA ht α hα j
  have hh : (1/2+A)/t ≤ 1/2 := by
    rw [div_le_iff₀ htpos]; linarith
  intro hz
  rw [hz, zero_sub, norm_neg, secondGammaPhaseCenter_norm] at hd
  linarith

/-- The actual two principal-log phases cancel. The remaining log error is
uniform in every bounded complex shift box. -/
theorem secondGammaPhaseLogError_norm_le {t A : ℝ}
    (hA : 0 ≤ A) (ht : 4*(A+1) ≤ t) (α : SecondMomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) :
    ‖secondGammaPhaseLogError t α‖ ≤ (2+4*A)/t := by
  have htpos : 0 < t := by linarith
  have ht2 : 0 < t/2 := by positivity
  have hb (j : Fin 2) :
      ‖Complex.log (secondGammaBase t α j)-Complex.log (t/2 : ℂ)-
        Complex.log (secondGammaPhaseCenter j)‖ ≤ 2*((1/2+A)/t) := by
    have hd := secondGammaBase_scaled_norm_le hA ht α hα j
    have hh : ‖secondGammaBase t α j/(t/2 : ℂ)-secondGammaPhaseCenter j‖ ≤ 1/2 := by
      apply hd.trans; rw [div_le_iff₀ htpos]; linarith
    have harg : |(Complex.log (secondGammaPhaseCenter j)).im| ≤ Real.pi/2 := by
      fin_cases j <;> simp [secondGammaPhaseCenter, Complex.log_I, Complex.log_neg_I,
        abs_of_nonneg (by positivity : 0 ≤ Real.pi/2)]
    have hl := principalLog_unit_near_bound (secondGammaPhaseCenter_norm j) harg hh
    have hlog := Complex.log_ofReal_mul ht2
      (secondGammaBase_scaled_ne_zero hA ht α hα j)
    push_cast at hlog
    rw [Complex.ofReal_log ht2.le] at hlog
    push_cast at hlog
    have he : (t/2 : ℂ)*(secondGammaBase t α j/(t/2 : ℂ)) =
        secondGammaBase t α j := by
      exact mul_div_cancel₀ _ (div_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne') (by norm_num))
    rw [he] at hlog
    rw [hlog]
    have he' : Complex.log (t/2 : ℂ)+Complex.log (secondGammaBase t α j/(t/2 : ℂ))-
        Complex.log (t/2 : ℂ)-Complex.log (secondGammaPhaseCenter j) =
        Complex.log (secondGammaBase t α j/(t/2 : ℂ))-
        Complex.log (secondGammaPhaseCenter j) := by ring
    rw [he']
    exact hl.trans (mul_le_mul_of_nonneg_left hd (by norm_num))
  unfold secondGammaPhaseLogError
  calc
    _ ≤ ∑ j : Fin 2, ‖Complex.log (secondGammaBase t α j)-Complex.log (t/2 : ℂ)-
        Complex.log (secondGammaPhaseCenter j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, 2*((1/2+A)/t) := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp; ring

/-- Exact exponential form of the actual Gamma principal-power phase. -/
theorem secondGammaMainPhase_eq_exp {t A : ℝ}
    (hA : 0 ≤ A) (ht : 4*(A+1) ≤ t) (α : SecondMomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) (z : ℂ) :
    secondGammaMainPhase t α z =
      Complex.exp ((z/2)*secondGammaPhaseLogError t α) := by
  have htpos : 0 < t := by linarith
  have ht2 : (t/2 : ℂ) ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne') (by norm_num)
  have hb (j : Fin 2) : secondGammaBase t α j ≠ 0 := by
    intro h; exact secondGammaBase_scaled_ne_zero hA ht α hα j (by rw [h]; simp)
  unfold secondGammaMainPhase
  simp_rw [Complex.cpow_def_of_ne_zero (hb _)]
  rw [← Complex.exp_sum, Complex.cpow_def_of_ne_zero ht2, ← Complex.exp_sub]
  congr 1
  unfold secondGammaPhaseLogError
  simp only [Fin.sum_univ_succ, Fin.isValue]
  simp [secondGammaPhaseCenter, Complex.log_I, Complex.log_neg_I]
  ring

/-- Quantitative error of the actual two principal powers, including their
upper/lower imaginary phase cancellation. -/
theorem secondGammaMainPhase_error_le {t A : ℝ}
    (hA : 0 ≤ A) (ht : 4*(A+1) ≤ t) (α : SecondMomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) (z : ℂ)
    (hz : (1+2*A)*‖z‖ ≤ t) :
    ‖secondGammaMainPhase t α z-1‖ ≤ (2+4*A)*‖z‖/t := by
  have htpos : 0 < t := by linarith
  rw [secondGammaMainPhase_eq_exp hA ht α hα z]
  have he : ‖(z/2)*secondGammaPhaseLogError t α‖ ≤ (1+2*A)*‖z‖/t := by
    rw [norm_mul, norm_div]
    have hb := secondGammaPhaseLogError_norm_le hA ht α hα
    calc
      _ ≤ (‖z‖/‖(2 : ℂ)‖)*((2+4*A)/t) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by norm_num; ring
  have hs : ‖(z/2)*secondGammaPhaseLogError t α‖ ≤ 1 :=
    he.trans ((div_le_iff₀ htpos).mpr (by simpa using hz))
  calc
    _ ≤ 2*‖(z/2)*secondGammaPhaseLogError t α‖ := Complex.norm_exp_sub_one_le hs
    _ ≤ 2*((1+2*A)*‖z‖/t) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring


/-- Each factor is normalized by its own actual principal power. -/
def secondNormalizedGammaFactor (t : ℝ) (α : SecondMomentShifts) (z : ℂ)
    (j : Fin 2) : ℂ :=
  (Gamma (secondGammaBase t α j+z/2)/Gamma (secondGammaBase t α j))/
    (secondGammaBase t α j)^(z/2)

private theorem secondGammaBase_im_lower {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (j : Fin 2) : t/4 ≤ |(secondGammaBase t α j).im| := by
  have hai := (abs_le.mp ((Complex.abs_im_le_norm (α j)).trans (hα j)))
  fin_cases j <;> simp [secondGammaBase, secondSourceZetaPoints, criticalLinePoint] <;>
    simp at hai <;> nlinarith [le_abs_self ((t+(α 0).im)/2),
      neg_le_abs ((-t+(α 1).im)/2)]

private theorem secondGammaBase_re_lower {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (j : Fin 2) : -|(secondGammaBase t α j).im| ≤ (secondGammaBase t α j).re := by
  have hr := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
  have hi := secondGammaBase_im_lower hA ht α hα j
  have he : (secondGammaBase t α j).re = (1/2+(α j).re)/2 := by
    fin_cases j <;> norm_num [secondGammaBase, secondSourceZetaPoints, criticalLinePoint]
  rw [he]
  linarith

/-- Actual individual Gamma factors are uniformly close to their principal
powers for arbitrary complex contour shifts satisfying the displayed bound. -/
theorem secondNormalizedGammaFactor_error_le {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (z : ℂ) (hz : 48*(‖z‖+‖z‖^2) < t) (j : Fin 2) :
    ‖secondNormalizedGammaFactor t α z j-1‖ ≤ 48*(‖z‖+‖z‖^2)/t := by
  have htpos : 0 < t := by linarith
  have hi := secondGammaBase_im_lower hA ht α hα j
  have hnz : ‖z/2‖ = ‖z‖/2 := by rw [norm_div]; norm_num
  have hs : 2 ≤ |(secondGammaBase t α j).im| := by linarith
  have hu : 24*(‖z/2‖+‖z/2‖^2) < |(secondGammaBase t α j).im| := by
    rw [hnz]; nlinarith [sq_nonneg ‖z‖, norm_nonneg z]
  have hb := Sechstmoment.gammaRatio_normalized_error_cone
    (secondGammaBase t α j) (z/2) (secondGammaBase_re_lower hA ht α hα j) hs hu
  unfold secondNormalizedGammaFactor
  apply hb.trans
  rw [hnz]
  have hipos : 0 < |(secondGammaBase t α j).im| := by linarith
  rw [div_le_div_iff₀ hipos htpos]
  nlinarith [sq_nonneg ‖z‖, norm_nonneg z]

/-- Two-factor error, with explicit constant. -/
theorem twofold_product_error_le (r : Fin 2 → ℂ) {E : ℝ}
    (hE : 0 ≤ E) (hE1 : E ≤ 1) (hr : ∀ j, ‖r j-1‖ ≤ E) :
    ‖(∏ j : Fin 2, r j)-1‖ ≤ 3*E := by
  have hn : ‖r 1‖ ≤ 2 := by
    have hb : ‖r 1‖ ≤ ‖r 1-1‖+1 := by
      convert norm_add_le (r 1-1) (1 : ℂ) using 1 <;> simp
    linarith [hr 1]
  have he : (∏ j : Fin 2, r j)-1 = (r 0-1)*r 1+(r 1-1) := by
    simp [Fin.prod_univ_succ]; ring
  rw [he]
  calc
    _ ≤ ‖(r 0-1)*r 1‖+‖r 1-1‖ := norm_add_le _ _
    _ ≤ E*2+E := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul (hr 0) hn (norm_nonneg _) hE) (hr 1)
    _ = _ := by ring


/-- Exact separation of the actual twofold quotient into its two normalized
Gamma errors and the cancelling principal-power phase. -/
theorem secondGammaQuotient_normalized_eq {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ A) (z : ℂ) :
    secondGammaQuotient t α z/(t/2 : ℂ)^z =
      (∏ j : Fin 2, secondNormalizedGammaFactor t α z j)*secondGammaMainPhase t α z := by
  have hi (j : Fin 2) := secondGammaBase_im_lower hA ht α hα j
  have hb (j : Fin 2) : secondGammaBase t α j ≠ 0 := by
    intro he
    have hj := hi j
    rw [he, Complex.zero_im, abs_zero] at hj
    linarith
  have hp : (∏ j : Fin 2, (secondGammaBase t α j)^(z/2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => by simp [hb j])
  have he (j : Fin 2) : (secondSourceZetaPoints t j+α j+z)/2 =
      secondGammaBase t α j+z/2 := by unfold secondGammaBase; ring
  unfold secondGammaQuotient secondNormalizedGammaFactor secondGammaMainPhase
  have hebase (j : Fin 2) : (secondSourceZetaPoints t j+α j)/2 = secondGammaBase t α j := rfl
  simp_rw [he, hebase]
  conv_rhs => lhs; rw [Finset.prod_div_distrib]
  field_simp
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  congr 2; ring

/-- A quantitative estimate for the actual twofold BBLR Gamma quotient,
with all phase factors retained and cancelled by proved identities. -/
theorem secondGammaQuotient_normalized_error_le {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (z : ℂ) (hz : 192*(‖z‖+‖z‖^2) < t)
    (hphase : (2+4*A)*‖z‖ ≤ t) :
    ‖secondGammaQuotient t α z/(t/2 : ℂ)^z-1‖ ≤
      (288*(‖z‖+‖z‖^2)+(2+4*A)*‖z‖)/t := by
  have htpos : 0 < t := by linarith
  have hnz : 0 ≤ ‖z‖+‖z‖^2 := by positivity
  have hz48 : 48*(‖z‖+‖z‖^2) < t := by linarith
  let E := 48*(‖z‖+‖z‖^2)/t
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hE1 : E ≤ 1 := by dsimp [E]; rw [div_le_iff₀ htpos]; linarith
  have herr (j : Fin 2) : ‖secondNormalizedGammaFactor t α z j-1‖ ≤ E :=
    secondNormalizedGammaFactor_error_le hA ht α hα z hz48 j
  have hp := twofold_product_error_le (secondNormalizedGammaFactor t α z) hE hE1 herr
  have hphase' : (1+2*A)*‖z‖ ≤ t := by nlinarith [norm_nonneg z]
  have htt : 4*(A+1) ≤ t := by linarith
  have hf := secondGammaMainPhase_error_le hA htt α hα z hphase'
  have hfn : ‖secondGammaMainPhase t α z‖ ≤ 2 := by
    have hh : ‖secondGammaMainPhase t α z‖ ≤ ‖secondGammaMainPhase t α z-1‖+1 := by
      convert norm_add_le (secondGammaMainPhase t α z-1) (1 : ℂ) using 1 <;> simp
    have hd : (2+4*A)*‖z‖/t ≤ 1 := (div_le_iff₀ htpos).mpr (by simpa using hphase)
    linarith
  rw [secondGammaQuotient_normalized_eq hA ht α hα z]
  have he : (∏ j : Fin 2, secondNormalizedGammaFactor t α z j)*secondGammaMainPhase t α z-1 =
      ((∏ j : Fin 2, secondNormalizedGammaFactor t α z j)-1)*secondGammaMainPhase t α z+
        (secondGammaMainPhase t α z-1) := by ring
  rw [he]
  calc
    _ ≤ ‖((∏ j : Fin 2, secondNormalizedGammaFactor t α z j)-1)*
        secondGammaMainPhase t α z‖+‖secondGammaMainPhase t α z-1‖ := norm_add_le _ _
    _ ≤ (3*E)*2+(2+4*A)*‖z‖/t := by rw [norm_mul]; gcongr
    _ = _ := by dsimp [E]; ring


/-- The same actual Gamma estimate in unnormalized form. -/
theorem secondGammaQuotient_error_le {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (z : ℂ) (hz : 192*(‖z‖+‖z‖^2) < t)
    (hphase : (2+4*A)*‖z‖ ≤ t) :
    ‖secondGammaQuotient t α z-(t/2 : ℂ)^z‖ ≤
      (t/2)^(z.re)*((288*(‖z‖+‖z‖^2)+(2+4*A)*‖z‖)/t) := by
  have htpos : 0 < t := by linarith
  have hbase : (t/2 : ℂ) ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne')
    (by norm_num)
  have hp : (t/2 : ℂ)^z ≠ 0 := by simp [hbase]
  have he : secondGammaQuotient t α z-(t/2 : ℂ)^z =
      (t/2 : ℂ)^z*(secondGammaQuotient t α z/(t/2 : ℂ)^z-1) := by
    field_simp
  have hn : ‖(t/2 : ℂ)^z‖ = (t/2)^(z.re) := by
    have hh := Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < t/2) z
    simpa using hh
  rw [he, norm_mul, hn]
  exact mul_le_mul_of_nonneg_left
    (secondGammaQuotient_normalized_error_le hA ht α hα z hz hphase) (by positivity)

private theorem second_eventually_mul_rpow_lt_id (C : ℝ) (hC : 0 < C)
    {e : ℝ} (he : e < 1) :
    ∀ᶠ t : ℝ in Filter.atTop, C*t^e < t := by
  have hlim : Filter.Tendsto (fun t : ℝ => t^e/t) Filter.atTop (𝓝 0) := by
    have hh := tendsto_rpow_neg_atTop (sub_pos.mpr he)
    apply hh.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [show -(1-e) = e-1 by ring, Real.rpow_sub ht, Real.rpow_one]
  filter_upwards [hlim.eventually_lt_const (one_div_pos.mpr hC),
    Filter.eventually_gt_atTop (0 : ℝ)] with t ht htpos
  rw [div_lt_iff₀ htpos] at ht
  have hh := mul_lt_mul_of_pos_left ht hC
  simpa [mul_assoc, hC.ne'] using hh

/-- The actual contour-shift estimate is uniform on a growing disk of radius
`t^ε`, for each fixed positive `ε < 1/2`. -/
theorem secondGammaQuotient_uniform_growing_disk {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (hεhalf : ε < 1/2) :
    ∀ᶠ t : ℝ in Filter.atTop, ∀ α : SecondMomentShifts, (∀ j, ‖α j‖ ≤ A) →
      ∀ z : ℂ, ‖z‖ ≤ t^ε →
        ‖secondGammaQuotient t α z/(t/2 : ℂ)^z-1‖ ≤
          (288*(‖z‖+‖z‖^2)+(2+4*A)*‖z‖)/t := by
  filter_upwards [second_eventually_mul_rpow_lt_id 384 (by norm_num) (by linarith : 2*ε < 1),
    second_eventually_mul_rpow_lt_id (2+4*A) (by linarith) (by linarith : ε < 1),
    Filter.eventually_ge_atTop (8*(A+1)), Filter.eventually_ge_atTop (1 : ℝ)]
    with t hz hphase ht ht1
  intro α hα z hzn
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hp : 1 ≤ t^ε := Real.one_le_rpow ht1 hε
  have hpow : (t^ε)^2 = t^(2*ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul htpos.le]
    congr 1; ring
  have hs : ‖z‖^2 ≤ t^(2*ε) := by rw [← hpow]; nlinarith [norm_nonneg z]
  have hl : ‖z‖ ≤ t^(2*ε) := by rw [← hpow]; nlinarith [norm_nonneg z]
  apply secondGammaQuotient_normalized_error_le hA ht α hα z
  · linarith
  · exact (mul_le_mul_of_nonneg_left hzn (by linarith : 0 ≤ 2+4*A)).trans hphase.le

/-- The actual Gamma-to-Gaussian replacement on the Mellin line. -/
def secondGammaGaussianReplacement (t : ℝ) (α : SecondMomentShifts) (z : ℂ) : ℂ :=
  Complex.exp (z^2)/z*(secondGammaQuotient t α z-(t/2 : ℂ)^z)

/-- Gaussian damping retains the explicit reciprocal-height saving. -/
theorem secondGammaGaussianReplacement_norm_le {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (z : ℂ) (hz : 192*(‖z‖+‖z‖^2) < t)
    (hphase : (2+4*A)*‖z‖ ≤ t) :
    ‖secondGammaGaussianReplacement t α z‖ ≤
      Real.exp ((z^2).re)/‖z‖*(t/2)^z.re*
        ((288*(‖z‖+‖z‖^2)+(2+4*A)*‖z‖)/t) := by
  unfold secondGammaGaussianReplacement
  rw [norm_mul, norm_div, Complex.norm_exp]
  have hb := secondGammaQuotient_error_le hA ht α hα z hz hphase
  exact (mul_le_mul_of_nonneg_left hb (by positivity)).trans_eq (by ring)

/-- Explicit polynomial-Gaussian control on each central vertical point. -/
theorem secondGammaGaussianReplacement_vertical_norm_le {t A c : ℝ}
    (hA : 0 ≤ A) (ht : 8*(A+1) ≤ t) (hc : 0 < c) (hc1 : c ≤ 1)
    (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ A) (v : ℝ)
    (hz : 192*(‖(c:ℂ)+(v:ℂ)*I‖+‖(c:ℂ)+(v:ℂ)*I‖^2) < t)
    (hphase : (2+4*A)*‖(c:ℂ)+(v:ℂ)*I‖ ≤ t) :
    ‖secondGammaGaussianReplacement t α ((c:ℂ)+(v:ℂ)*I)‖ ≤
      Real.exp (c^2)*(t/2)^c*(578+4*A)/(c*t)*
        ((1+|v|)^2*Real.exp (-v^2)) := by
  have htp : 0 < t := by linarith
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hzr : z.re = c := by simp [z]
  have hzi : z.im = v := by simp [z]
  have hzn : c ≤ ‖z‖ := by
    simpa only [hzr, abs_of_pos hc] using Complex.abs_re_le_norm z
  have hzne : 0 < ‖z‖ := hc.trans_le hzn
  have hnup : ‖z‖ ≤ 1+|v| := by
    calc
      _ ≤ ‖(c:ℂ)‖+‖(v:ℂ)*I‖ := norm_add_le _ _
      _ = c+|v| := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
      _ ≤ _ := by linarith
  have hs : (z^2).re = c^2-v^2 := by simp [pow_two, Complex.mul_re, hzr, hzi]
  have hp : 288*(‖z‖+‖z‖^2)+(2+4*A)*‖z‖ ≤ (578+4*A)*(1+|v|)^2 := by
    have h1 : 1 ≤ 1+|v| := by linarith [abs_nonneg v]
    have hsq : ‖z‖^2 ≤ (1+|v|)^2 := by nlinarith [norm_nonneg z]
    have hlin : ‖z‖ ≤ (1+|v|)^2 := by nlinarith [norm_nonneg z]
    nlinarith [mul_le_mul_of_nonneg_left hlin (by positivity : 0 ≤ 2+4*A)]
  have hb := secondGammaGaussianReplacement_norm_le hA ht α hα z hz hphase
  rw [hs, hzr] at hb
  apply hb.trans
  have hdiv : Real.exp (c^2-v^2)/‖z‖ ≤ Real.exp (c^2-v^2)/c := by
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le hc hzn
  calc
    _ ≤ Real.exp (c^2-v^2)/c*(t/2)^c*((578+4*A)*(1+|v|)^2/t) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hdiv (by positivity)
      · exact div_le_div_of_nonneg_right hp htp.le
      · positivity
      · positivity
    _ = _ := by rw [show c^2-v^2 = c^2+(-v^2) by ring, Real.exp_add]; ring

/-- The four normalized factors of the even two-factor pole killer. -/
def secondPoleCorrectionBases (s r : ℂ) : Fin 4 → ℂ := ![s,1-s,r,1-r]

def secondPoleCorrection (s r z : ℂ) : ℂ :=
  ∏ j : Fin 4, (1-z^2/(secondPoleCorrectionBases s r j)^2)

/-- Algebraic factorization of the actual normalized pole-killer polynomial. -/
theorem secondPoleCorrection_eq {s r : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1)
    (hr : r ≠ 0) (hr1 : r ≠ 1) (z : ℂ) :
    secondPoleCorrection s r z =
      ((s+z)*(1-s-z)*(s-z)*(1-s+z)*(r+z)*(1-r-z)*(r-z)*(1-r+z)) /
        (s*(1-s)*r*(1-r))^2 := by
  have hs' : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hr' : 1-r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  simp only [secondPoleCorrection, Fin.prod_univ_succ, Fin.isValue]
  simp [secondPoleCorrectionBases]
  field_simp
  ring

/-- The correction is O(z²/H²) once all four moving roots have size H. -/
theorem secondPoleCorrection_error_le {H : ℝ} (hH : 0 < H) (s r z : ℂ)
    (hbase : ∀ j, H ≤ ‖secondPoleCorrectionBases s r j‖)
    (hz : ‖z‖^2 ≤ H^2) :
    ‖secondPoleCorrection s r z-1‖ ≤ 15*‖z‖^2/H^2 := by
  let E : ℝ := ‖z‖^2/H^2
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hE1 : E ≤ 1 := by
    dsimp [E]
    exact (div_le_iff₀ (sq_pos_of_pos hH)).mpr (by simpa using hz)
  have hrj (j : Fin 4) :
      ‖(1-z^2/(secondPoleCorrectionBases s r j)^2)-1‖ ≤ E := by
    have hd : H^2 ≤ ‖secondPoleCorrectionBases s r j‖^2 :=
      pow_le_pow_left₀ hH.le (hbase j) 2
    have he : (1-z^2/(secondPoleCorrectionBases s r j)^2)-1 =
        -(z^2/(secondPoleCorrectionBases s r j)^2) := by ring
    rw [he, norm_neg, norm_div, norm_pow, norm_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hH) hd
  exact (fourfold_product_error_le _ hE hE1 hrj).trans_eq (by dsimp [E]; ring)

/-- On a bounded shift box every pole-killer root has size at least t/2. -/
theorem secondPoleCorrectionBases_norm_lower {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (j : Fin 4) :
    t/2 ≤ ‖secondPoleCorrectionBases
      (secondSourceZetaPoints t 0+α 0) (secondSourceZetaPoints t 1+α 1) j‖ := by
  have h0 := secondGammaBase_im_lower hA ht α hα 0
  have h1 := secondGammaBase_im_lower hA ht α hα 1
  have hs0 : |(secondSourceZetaPoints t 0+α 0).im| ≥ t/2 := by
    have he : (secondGammaBase t α 0).im = (secondSourceZetaPoints t 0+α 0).im/2 := by
      simp [secondGammaBase]
    rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h0
    linarith
  have hs1 : |(secondSourceZetaPoints t 1+α 1).im| ≥ t/2 := by
    have he : (secondGammaBase t α 1).im = (secondSourceZetaPoints t 1+α 1).im/2 := by
      simp [secondGammaBase]
    rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
    linarith
  have hb : ∀ k : Fin 4, t/2 ≤ |(secondPoleCorrectionBases
      (secondSourceZetaPoints t 0+α 0) (secondSourceZetaPoints t 1+α 1) k).im| := by
    intro k
    fin_cases k
    · change t/2 ≤ |(secondSourceZetaPoints t 0+α 0).im|
      exact hs0
    · change t/2 ≤ |(1-(secondSourceZetaPoints t 0+α 0)).im|
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      exact hs0
    · change t/2 ≤ |(secondSourceZetaPoints t 1+α 1).im|
      exact hs1
    · change t/2 ≤ |(1-(secondSourceZetaPoints t 1+α 1)).im|
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
      exact hs1
  exact (hb j).trans (Complex.abs_im_le_norm _)

/-- The actual two-factor Gaussian pole-killer differs by O(z²/t²). -/
theorem secondPoleCorrection_shifted_error_le {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (z : ℂ) (hz : 4*‖z‖^2 ≤ t^2) :
    ‖secondPoleCorrection (secondSourceZetaPoints t 0+α 0)
      (secondSourceZetaPoints t 1+α 1) z-1‖ ≤ 60*‖z‖^2/t^2 := by
  have htp : 0 < t := by linarith
  have hb := secondPoleCorrection_error_le (by positivity : 0 < t/2)
    (secondSourceZetaPoints t 0+α 0) (secondSourceZetaPoints t 1+α 1) z
    (secondPoleCorrectionBases_norm_lower hA ht α hα)
    (by nlinarith : ‖z‖^2 ≤ (t/2)^2)
  exact hb.trans_eq (by field_simp; ring)

/-- Duplicate each member of the pair in the already proved four-Gamma bound. -/
def secondDuplicatedShifts (α : SecondMomentShifts) : MomentShifts :=
  ![α 0, α 0, α 1, α 1]

theorem secondGammaQuotient_sq (t : ℝ) (α : SecondMomentShifts) (z : ℂ) :
    bblrGammaQuotient t (secondDuplicatedShifts α) z =
      (secondGammaQuotient t α z)^2 := by
  simp [bblrGammaQuotient, secondGammaQuotient, secondDuplicatedShifts,
    sourceZetaPoints, secondSourceZetaPoints, Fin.prod_univ_succ]
  ring

/-- Global polynomial envelope on the whole positive strip, including the
exterior of the central Gamma-ratio disk. -/
theorem secondGammaQuotient_polynomial_positive_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ t v c : ℝ, 0 ≤ t → 0 ≤ c → c ≤ 1 →
      ∀ α : SecondMomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
        ‖secondGammaQuotient t α ((c:ℂ)+(v:ℂ)*I)‖ ≤ C*(2+t+|v|)^4 := by
  obtain ⟨C, hC, hb⟩ := bblrGammaQuotient_polynomial_positive_strip_bound
  refine ⟨Real.sqrt C, by positivity, ?_⟩
  intro t v c ht hc hc1 α hα
  have ha : ∀ j, ‖secondDuplicatedShifts α j‖ ≤ 1/4 := by
    intro j
    fin_cases j
    · simpa [secondDuplicatedShifts] using hα 0
    · simpa [secondDuplicatedShifts] using hα 0
    · simpa [secondDuplicatedShifts] using hα 1
    · simpa [secondDuplicatedShifts] using hα 1
  have hs := hb t v c ht hc hc1 (secondDuplicatedShifts α) ha
  rw [secondGammaQuotient_sq, norm_pow] at hs
  have he : (Real.sqrt C*(2+t+|v|)^4)^2 = C*(2+t+|v|)^8 := by
    rw [mul_pow, Real.sq_sqrt hC.le]
    ring
  have hn : 0 ≤ Real.sqrt C*(2+t+|v|)^4 := by positivity
  rw [←he] at hs
  nlinarith [norm_nonneg (secondGammaQuotient t α ((c:ℂ)+(v:ℂ)*I))]

/-- A fixed finite Gaussian moment used by the concrete central replacement. -/
def secondGaussianQuadraticMass : ℝ :=
  ∫ v : ℝ, (1+|v|)^2*Real.exp (-v^2)

theorem secondGaussianQuadraticMass_nonneg : 0 ≤ secondGaussianQuadraticMass :=
  integral_nonneg (fun _ => by positivity)

theorem secondGaussianQuadraticMajorant_integrable :
    Integrable (fun v : ℝ => (1+|v|)^2*Real.exp (-v^2)) := by
  simpa only [zero_mul, zero_sub] using
    Sechstmoment.gaussianPolynomialExponential_integrable 2 0

/-- Integrating the actual replacement over any admissible central segment
preserves the reciprocal-height saving, with a fixed Gaussian constant. -/
theorem secondGammaGaussianReplacement_central_integral_norm_le {t A c H : ℝ}
    (hA : 0 ≤ A) (ht : 8*(A+1) ≤ t) (hc : 0 < c) (hc1 : c ≤ 1)
    (α : SecondMomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (hz : ∀ v ∈ Icc (-H) H,
      192*(‖(c:ℂ)+(v:ℂ)*I‖+‖(c:ℂ)+(v:ℂ)*I‖^2) < t)
    (hphase : ∀ v ∈ Icc (-H) H, (2+4*A)*‖(c:ℂ)+(v:ℂ)*I‖ ≤ t) :
    ‖∫ v in Icc (-H) H, secondGammaGaussianReplacement t α ((c:ℂ)+(v:ℂ)*I)‖ ≤
      Real.exp (c^2)*(t/2)^c*(578+4*A)/(c*t)*secondGaussianQuadraticMass := by
  have htp : 0 < t := by linarith
  let B : ℝ := Real.exp (c^2)*(t/2)^c*(578+4*A)/(c*t)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hgi : Integrable (fun v : ℝ => B*((1+|v|)^2*Real.exp (-v^2))) :=
    secondGaussianQuadraticMajorant_integrable.const_mul B
  have hpoint : ∀ᵐ (v : ℝ) ∂volume.restrict (Icc (-H) H),
      ‖secondGammaGaussianReplacement t α ((c:ℂ)+(v:ℂ)*I)‖ ≤
        B*((1+|v|)^2*Real.exp (-v^2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact secondGammaGaussianReplacement_vertical_norm_le hA ht hc hc1 α hα v
      (hz v hv) (hphase v hv)
  calc
    _ ≤ ∫ v in Icc (-H) H, B*((1+|v|)^2*Real.exp (-v^2)) :=
      norm_integral_le_of_norm_le hgi.integrableOn hpoint
    _ ≤ ∫ v : ℝ, B*((1+|v|)^2*Real.exp (-v^2)) :=
      setIntegral_le_integral hgi (Eventually.of_forall (fun _ => by positivity))
    _ = _ := by rw [integral_const_mul]; rfl

@[simp] theorem secondSourceZetaPoints_re (t : ℝ) (j : Fin 2) :
    (secondSourceZetaPoints t j).re = 1/2 := by
  fin_cases j <;> norm_num [secondSourceZetaPoints, criticalLinePoint]

/-- The actual pair quotient is continuous throughout each positive line. -/
theorem secondGammaQuotient_continuous_positive_line (α : SecondMomentShifts)
    (t c : ℝ) (hc : 0 ≤ c) (hα : ∀ j, -1/2 < (α j).re) :
    Continuous (fun v : ℝ => secondGammaQuotient t α ((c:ℂ)+(v:ℂ)*I)) := by
  unfold secondGammaQuotient
  apply continuous_finsetProd
  intro j hj
  apply Continuous.div_const
  apply continuous_iff_continuousAt.mpr
  intro v
  apply (Complex.continuousAt_Gamma _ ?_).comp
  · fun_prop
  · intro n hn
    have hr := congrArg Complex.re hn
    have ha := hα j
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    simp at hr
    linarith

/-- The two-Gamma Gaussian kernel before the harmless real Mellin powers. -/
def secondGammaGaussianKernel (t : ℝ) (α : SecondMomentShifts) (c v : ℝ) : ℂ :=
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  Complex.exp (z^2)/z*secondGammaQuotient t α z

/-- The polynomial envelope and Gaussian dominate the complete vertical line. -/
theorem secondGammaGaussianKernel_global_majorant :
    ∃ C : ℝ, 0 < C ∧ ∀ t c : ℝ, 0 ≤ t → 0 < c → c ≤ 1 →
      ∀ α : SecondMomentShifts, (∀ j, ‖α j‖ ≤ 1/4) → ∀ v : ℝ,
        ‖secondGammaGaussianKernel t α c v‖ ≤
          C*(2+t)^4/c*(1+|v|)^4*Real.exp (-v^2) := by
  obtain ⟨C, hC, hb⟩ := secondGammaQuotient_polynomial_positive_strip_bound
  refine ⟨Real.exp 1*C, by positivity, ?_⟩
  intro t c ht hc hc1 α hα v
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hzr : z.re = c := by simp [z]
  have hzi : z.im = v := by simp [z]
  have hzn : c ≤ ‖z‖ := by
    simpa only [hzr, abs_of_pos hc] using Complex.abs_re_le_norm z
  have hs : (z^2).re = c^2-v^2 := by simp [pow_two, Complex.mul_re, hzr, hzi]
  have hg : ‖Complex.exp (z^2)/z‖ ≤ Real.exp 1/c*Real.exp (-v^2) := by
    rw [norm_div, Complex.norm_exp, hs,
      show c^2-v^2 = c^2+(-v^2) by ring, Real.exp_add]
    have hc2 : c^2 ≤ 1 := by nlinarith
    calc
      _ ≤ (Real.exp 1*Real.exp (-v^2))/c := by
        apply div_le_div₀ (by positivity)
        · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hc2) (by positivity)
        · exact hc
        · exact hzn
      _ = _ := by ring
  have hp : (2+t+|v|)^4 ≤ (2+t)^4*(1+|v|)^4 := by
    rw [←mul_pow]
    gcongr
    nlinarith [abs_nonneg v]
  have hq := (hb t v c ht hc.le hc1 α hα).trans
    (mul_le_mul_of_nonneg_left hp hC.le)
  unfold secondGammaGaussianKernel
  change ‖Complex.exp (z^2)/z*secondGammaQuotient t α z‖ ≤ _
  rw [norm_mul]
  exact (mul_le_mul hg hq (norm_nonneg _) (by positivity)).trans_eq (by ring)

/-- All actual quotient kernels are integrable; no tail premise is assumed. -/
theorem secondGammaGaussianKernel_integrable (t c : ℝ) (ht : 0 ≤ t)
    (hc : 0 < c) (hc1 : c ≤ 1) (α : SecondMomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ 1/4) :
    Integrable (secondGammaGaussianKernel t α c) := by
  obtain ⟨C, _hC, hb⟩ := secondGammaGaussianKernel_global_majorant
  have har : ∀ j, -1/2 < (α j).re := by
    intro j
    have ha := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
    linarith
  have hcont : Continuous (secondGammaGaussianKernel t α c) := by
    unfold secondGammaGaussianKernel
    apply Continuous.mul
    · apply Continuous.div
      · fun_prop
      · fun_prop
      · intro v hv
        have hr := congrArg Complex.re hv
        simp at hr
        linarith
    · exact secondGammaQuotient_continuous_positive_line α t c hc.le har
  have hgi : Integrable (fun v : ℝ => (1+|v|)^4*Real.exp (-v^2)) := by
    simpa only [zero_mul, zero_sub] using
      Sechstmoment.gaussianPolynomialExponential_integrable 4 0
  apply (hgi.const_mul (C*(2+t)^4/c)).mono' hcont.aestronglyMeasurable
  exact Eventually.of_forall (fun v => by
    simpa only [mul_assoc] using hb t c ht hc hc1 α hα v)

/-- An explicit actual Gamma-kernel tail with Gaussian decay. -/
theorem secondGammaGaussianKernel_tail_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t c R : ℝ, 0 ≤ t → 0 < c → c ≤ 1 → 0 ≤ R →
      ∀ α : SecondMomentShifts, (∀ j, ‖α j‖ ≤ 1/4) →
        ‖∫ v in {v : ℝ | R < |v|}, secondGammaGaussianKernel t α c v‖ ≤
          C*(2+t)^4/c*gaussianTailConstant 4*Real.exp (-(1/2)*R^2) := by
  obtain ⟨C, hC, hb⟩ := secondGammaGaussianKernel_global_majorant
  refine ⟨C, hC, ?_⟩
  intro t c R ht hc hc1 hR α hα
  exact gaussian_integral_tail_norm_le _
    (secondGammaGaussianKernel_integrable t c ht hc hc1 α hα) 4
    (by positivity) hR (hb t c ht hc hc1 α hα)

/-- The actual pole-killed quotient relative to the Gaussian leading power. -/
def secondPoleCorrectedGammaQuotient (t : ℝ) (α : SecondMomentShifts) (z : ℂ) : ℂ :=
  secondPoleCorrection (secondSourceZetaPoints t 0+α 0)
    (secondSourceZetaPoints t 1+α 1) z*secondGammaQuotient t α z

/-- The moving pole-killer correction and Gamma error are both controlled
from their explicit formulas, without a replacement-error premise. -/
theorem secondPoleCorrectedGammaQuotient_normalized_error_le {t A : ℝ}
    (hA : 0 ≤ A) (ht : 8*(A+1) ≤ t) (α : SecondMomentShifts)
    (hα : ∀ j, ‖α j‖ ≤ A) (z : ℂ)
    (hz : 192*(‖z‖+‖z‖^2) < t) (hphase : (2+4*A)*‖z‖ ≤ t) :
    ‖secondPoleCorrectedGammaQuotient t α z/(t/2 : ℂ)^z-1‖ ≤
      2*((288*(‖z‖+‖z‖^2)+(2+4*A)*‖z‖)/t)+60*‖z‖^2/t^2 := by
  have htp : 0 < t := by linarith
  have ht8 : 8 ≤ t := by linarith
  have hzs : 4*‖z‖^2 ≤ t^2 := by nlinarith [norm_nonneg z, sq_nonneg ‖z‖, sq_nonneg (t-1)]
  let P := secondPoleCorrection (secondSourceZetaPoints t 0+α 0)
    (secondSourceZetaPoints t 1+α 1) z
  have hp : ‖P-1‖ ≤ 60*‖z‖^2/t^2 :=
    secondPoleCorrection_shifted_error_le hA ht α hα z hzs
  have hp1 : 60*‖z‖^2/t^2 ≤ 1 := by
    rw [div_le_iff₀ (sq_pos_of_pos htp)]
    nlinarith [norm_nonneg z, sq_nonneg ‖z‖, sq_nonneg (t-1)]
  have hpn : ‖P‖ ≤ 2 := by
    have hh : ‖P‖ ≤ ‖P-1‖+1 := by
      convert norm_add_le (P-1) (1:ℂ) using 1 <;> simp
    linarith
  have hq := secondGammaQuotient_normalized_error_le hA ht α hα z hz hphase
  unfold secondPoleCorrectedGammaQuotient
  change ‖P*secondGammaQuotient t α z/(t/2:ℂ)^z-1‖ ≤ _
  rw [mul_div_assoc]
  have he : P*(secondGammaQuotient t α z/(t/2:ℂ)^z)-1 =
      P*(secondGammaQuotient t α z/(t/2:ℂ)^z-1)+(P-1) := by ring
  rw [he]
  calc
    _ ≤ ‖P*(secondGammaQuotient t α z/(t/2:ℂ)^z-1)‖+‖P-1‖ := norm_add_le _ _
    _ ≤ 2*((288*(‖z‖+‖z‖^2)+(2+4*A)*‖z‖)/t)+60*‖z‖^2/t^2 := by
      rw [norm_mul]
      exact add_le_add (mul_le_mul hpn hq (norm_nonneg _) (by norm_num)) hp

/-- Global polynomial norm control, including zero moving roots under Lean's
 total division convention. This supplies a genuine full-line majorant. -/
theorem secondPoleCorrection_polynomial_norm_le (s r z : ℂ) :
    ‖secondPoleCorrection s r z‖ ≤
      (∏ j : Fin 4, (1+‖(secondPoleCorrectionBases s r j)^2‖⁻¹))*(1+‖z‖)^8 := by
  have hfactor (j : Fin 4) :
      ‖1-z^2/(secondPoleCorrectionBases s r j)^2‖ ≤
        (1+‖(secondPoleCorrectionBases s r j)^2‖⁻¹)*(1+‖z‖)^2 := by
    have hh := norm_sub_le (1:ℂ) (z^2/(secondPoleCorrectionBases s r j)^2)
    rw [norm_one, norm_div, norm_pow, div_eq_mul_inv] at hh
    have h1 : (1:ℝ) ≤ (1+‖z‖)^2 := by nlinarith [norm_nonneg z]
    have h2 : ‖z‖^2 ≤ (1+‖z‖)^2 := by nlinarith [norm_nonneg z]
    apply hh.trans
    calc
      _ ≤ (1+‖z‖)^2+(1+‖z‖)^2*‖(secondPoleCorrectionBases s r j)^2‖⁻¹ :=
        add_le_add h1 (mul_le_mul_of_nonneg_right h2 (by positivity))
      _ = _ := by ring
  unfold secondPoleCorrection
  rw [norm_prod]
  calc
    _ ≤ ∏ j : Fin 4,
        (1+‖(secondPoleCorrectionBases s r j)^2‖⁻¹)*(1+‖z‖)^2 :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => hfactor j)
    _ = _ := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      ring

theorem secondGammaHalf_ne_zero {t : ℝ} (ht : 0 < t) : (t/2:ℂ) ≠ 0 :=
  div_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') (by norm_num)

theorem secondGammaHalf_log {t : ℝ} (ht : 0 < t) :
    Complex.log (t/2:ℂ) = (Real.log (t/2):ℂ) := by
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    (Complex.ofReal_log (by positivity : 0 ≤ t/2)).symm

theorem secondGammaHalfPower_norm {t : ℝ} (ht : 0 < t) (z : ℂ) :
    ‖(t/2:ℂ)^z‖ = (t/2)^z.re := by
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < t/2) z

end
end Sechstmoment.Source
