import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.GCongr
import Sechstmoment.Zeta.AFE.Four.PhaseComparison
import Sechstmoment.Zeta.Centering.GammaRatio


namespace Sechstmoment.Source
open Complex Filter
open scoped BigOperators Topology
noncomputable section

def bblrNormalizedGammaFactor (t : ℝ) (α : MomentShifts) (z : ℂ)
    (j : Fin 4) : ℂ :=
  (Gamma (bblrGammaBase t α j+z/2)/Gamma (bblrGammaBase t α j))/
    (bblrGammaBase t α j)^(z/2)

private theorem bblrGammaBase_im_lower {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (j : Fin 4) : t/4 ≤ |(bblrGammaBase t α j).im| := by
  have hai := (abs_le.mp ((Complex.abs_im_le_norm (α j)).trans (hα j)))
  fin_cases j <;> simp [bblrGammaBase, sourceZetaPoints, criticalLinePoint] <;>
    simp at hai <;> nlinarith [le_abs_self ((t+(α 0).im)/2),
      le_abs_self ((t+(α 1).im)/2), neg_le_abs ((-t+(α 2).im)/2),
      neg_le_abs ((-t+(α 3).im)/2)]

private theorem bblrGammaBase_re_lower {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (j : Fin 4) : -|(bblrGammaBase t α j).im| ≤ (bblrGammaBase t α j).re := by
  have hr := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
  have hi := bblrGammaBase_im_lower hA ht α hα j
  have he : (bblrGammaBase t α j).re = (1/2+(α j).re)/2 := by
    fin_cases j <;> simp [bblrGammaBase, sourceZetaPoints, criticalLinePoint] <;> norm_num
  rw [he]
  linarith

theorem bblrNormalizedGammaFactor_error_le {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (z : ℂ) (hz : 48*(‖z‖+‖z‖^2) < t) (j : Fin 4) :
    ‖bblrNormalizedGammaFactor t α z j-1‖ ≤ 48*(‖z‖+‖z‖^2)/t := by
  have htpos : 0 < t := by linarith
  have hi := bblrGammaBase_im_lower hA ht α hα j
  have hnz : ‖z/2‖ = ‖z‖/2 := by rw [norm_div]; norm_num
  have hs : 2 ≤ |(bblrGammaBase t α j).im| := by linarith
  have hu : 24*(‖z/2‖+‖z/2‖^2) < |(bblrGammaBase t α j).im| := by
    rw [hnz]; nlinarith [sq_nonneg ‖z‖, norm_nonneg z]
  have hb := Sechstmoment.gammaRatio_normalized_error_cone
    (bblrGammaBase t α j) (z/2) (bblrGammaBase_re_lower hA ht α hα j) hs hu
  unfold bblrNormalizedGammaFactor
  apply hb.trans
  rw [hnz]
  have hipos : 0 < |(bblrGammaBase t α j).im| := by linarith
  rw [div_le_div_iff₀ hipos htpos]
  nlinarith [sq_nonneg ‖z‖, norm_nonneg z]

theorem fourfold_product_error_le (r : Fin 4 → ℂ) {E : ℝ}
    (hE : 0 ≤ E) (hE1 : E ≤ 1) (hr : ∀ j, ‖r j-1‖ ≤ E) :
    ‖(∏ j : Fin 4, r j)-1‖ ≤ 15*E := by
  have hn (j : Fin 4) : ‖r j‖ ≤ 2 := by
    have hb : ‖r j‖ ≤ ‖r j-1‖+1 := by
      convert norm_add_le (r j-1) (1 : ℂ) using 1 <;> simp
    linarith [hr j]
  have he : (∏ j : Fin 4, r j)-1 =
      (r 0-1)*r 1*r 2*r 3+(r 1-1)*r 2*r 3+(r 2-1)*r 3+(r 3-1) := by
    simp [Fin.prod_univ_succ]; ring
  have h0 : ‖(r 0-1)*r 1*r 2*r 3‖ ≤ 8*E := by
    simp only [norm_mul]; calc
      _ ≤ E*2*2*2 := by gcongr <;> first | exact hr _ | exact hn _
      _ = _ := by ring
  have h1 : ‖(r 1-1)*r 2*r 3‖ ≤ 4*E := by
    simp only [norm_mul]; calc
      _ ≤ E*2*2 := by gcongr <;> first | exact hr _ | exact hn _
      _ = _ := by ring
  have h2 : ‖(r 2-1)*r 3‖ ≤ 2*E := by
    simp only [norm_mul]; calc
      _ ≤ E*2 := by gcongr <;> first | exact hr _ | exact hn _
      _ = _ := by ring
  rw [he]
  have hsum := norm_add_le ((r 0-1)*r 1*r 2*r 3+(r 1-1)*r 2*r 3+(r 2-1)*r 3) (r 3-1)
  have hsum2 := norm_add_le ((r 0-1)*r 1*r 2*r 3+(r 1-1)*r 2*r 3) ((r 2-1)*r 3)
  have hsum3 := norm_add_le ((r 0-1)*r 1*r 2*r 3) ((r 1-1)*r 2*r 3)
  linarith [hr 3]


theorem bblrGammaQuotient_normalized_eq {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A) (z : ℂ) :
    bblrGammaQuotient t α z/(t/2 : ℂ)^(2*z) =
      (∏ j : Fin 4, bblrNormalizedGammaFactor t α z j)*bblrGammaMainPhase t α z := by
  have hi (j : Fin 4) := bblrGammaBase_im_lower hA ht α hα j
  have hb (j : Fin 4) : bblrGammaBase t α j ≠ 0 := by
    intro he
    have hj := hi j
    rw [he, Complex.zero_im, abs_zero] at hj
    linarith
  have hp : (∏ j : Fin 4, (bblrGammaBase t α j)^(z/2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => by simp [hb j])
  have he (j : Fin 4) : (sourceZetaPoints t j+α j+z)/2 =
      bblrGammaBase t α j+z/2 := by unfold bblrGammaBase; ring
  unfold bblrGammaQuotient bblrNormalizedGammaFactor bblrGammaMainPhase
  have hebase (j : Fin 4) : (sourceZetaPoints t j+α j)/2 = bblrGammaBase t α j := rfl
  simp_rw [he, hebase]
  conv_rhs => lhs; rw [Finset.prod_div_distrib]
  field_simp
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  congr 2; ring

theorem bblrGammaQuotient_normalized_error_le {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (z : ℂ) (hz : 192*(‖z‖+‖z‖^2) < t)
    (hphase : (4+8*A)*‖z‖ ≤ t) :
    ‖bblrGammaQuotient t α z/(t/2 : ℂ)^(2*z)-1‖ ≤
      (1440*(‖z‖+‖z‖^2)+(4+8*A)*‖z‖)/t := by
  have htpos : 0 < t := by linarith
  have hnz : 0 ≤ ‖z‖+‖z‖^2 := by positivity
  have hz48 : 48*(‖z‖+‖z‖^2) < t := by linarith
  let E := 48*(‖z‖+‖z‖^2)/t
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hE1 : E ≤ 1 := by dsimp [E]; rw [div_le_iff₀ htpos]; linarith
  have herr (j : Fin 4) : ‖bblrNormalizedGammaFactor t α z j-1‖ ≤ E :=
    bblrNormalizedGammaFactor_error_le hA ht α hα z hz48 j
  have hp := fourfold_product_error_le (bblrNormalizedGammaFactor t α z) hE hE1 herr
  have hphase' : (2+4*A)*‖z‖ ≤ t := by nlinarith [norm_nonneg z]
  have htt : 4*(A+1) ≤ t := by linarith
  have hf := bblrGammaMainPhase_error_le hA htt α hα z hphase'
  have hfn : ‖bblrGammaMainPhase t α z‖ ≤ 2 := by
    have hh : ‖bblrGammaMainPhase t α z‖ ≤ ‖bblrGammaMainPhase t α z-1‖+1 := by
      convert norm_add_le (bblrGammaMainPhase t α z-1) (1 : ℂ) using 1 <;> simp
    have hd : (4+8*A)*‖z‖/t ≤ 1 := (div_le_iff₀ htpos).mpr (by simpa using hphase)
    linarith
  rw [bblrGammaQuotient_normalized_eq hA ht α hα z]
  have he : (∏ j : Fin 4, bblrNormalizedGammaFactor t α z j)*bblrGammaMainPhase t α z-1 =
      ((∏ j : Fin 4, bblrNormalizedGammaFactor t α z j)-1)*bblrGammaMainPhase t α z+
        (bblrGammaMainPhase t α z-1) := by ring
  rw [he]
  calc
    _ ≤ ‖((∏ j : Fin 4, bblrNormalizedGammaFactor t α z j)-1)*
        bblrGammaMainPhase t α z‖+‖bblrGammaMainPhase t α z-1‖ := norm_add_le _ _
    _ ≤ (15*E)*2+(4+8*A)*‖z‖/t := by rw [norm_mul]; gcongr
    _ = _ := by dsimp [E]; ring


theorem bblrGammaQuotient_error_le {t A : ℝ} (hA : 0 ≤ A)
    (ht : 8*(A+1) ≤ t) (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ A)
    (z : ℂ) (hz : 192*(‖z‖+‖z‖^2) < t)
    (hphase : (4+8*A)*‖z‖ ≤ t) :
    ‖bblrGammaQuotient t α z-(t/2 : ℂ)^(2*z)‖ ≤
      (t/2)^(2*z.re)*((1440*(‖z‖+‖z‖^2)+(4+8*A)*‖z‖)/t) := by
  have htpos : 0 < t := by linarith
  have hbase : (t/2 : ℂ) ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne')
    (by norm_num)
  have hp : (t/2 : ℂ)^(2*z) ≠ 0 := by simp [hbase]
  have he : bblrGammaQuotient t α z-(t/2 : ℂ)^(2*z) =
      (t/2 : ℂ)^(2*z)*(bblrGammaQuotient t α z/(t/2 : ℂ)^(2*z)-1) := by
    field_simp
  have hn : ‖(t/2 : ℂ)^(2*z)‖ = (t/2)^(2*z.re) := by
    have hh := Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < t/2) (2*z)
    simpa using hh
  rw [he, norm_mul, hn]
  exact mul_le_mul_of_nonneg_left
    (bblrGammaQuotient_normalized_error_le hA ht α hα z hz hphase) (by positivity)

private theorem eventually_mul_rpow_lt_id (C : ℝ) (hC : 0 < C)
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

theorem bblrGammaQuotient_uniform_growing_disk {A ε : ℝ}
    (hA : 0 ≤ A) (hε : 0 ≤ ε) (hεhalf : ε < 1/2) :
    ∀ᶠ t : ℝ in Filter.atTop, ∀ α : MomentShifts, (∀ j, ‖α j‖ ≤ A) →
      ∀ z : ℂ, ‖z‖ ≤ t^ε →
        ‖bblrGammaQuotient t α z/(t/2 : ℂ)^(2*z)-1‖ ≤
          (1440*(‖z‖+‖z‖^2)+(4+8*A)*‖z‖)/t := by
  filter_upwards [eventually_mul_rpow_lt_id 384 (by norm_num) (by linarith : 2*ε < 1),
    eventually_mul_rpow_lt_id (4+8*A) (by linarith) (by linarith : ε < 1),
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
  apply bblrGammaQuotient_normalized_error_le hA ht α hα z
  · linarith
  · exact (mul_le_mul_of_nonneg_left hzn (by linarith : 0 ≤ 4+8*A)).trans hphase.le

end
end Sechstmoment.Source
