import Mathlib.Analysis.Complex.RemovableSingularity
import SixthMoment.Zeta.AFE.Four.GammaComparison

namespace SixthMoment.Source
open Complex Set Metric
open scoped BigOperators Topology
noncomputable section

def bblrCentralNormalizedGamma (t : ℝ) (α : MomentShifts) (z : ℂ) : ℂ :=
  bblrGammaQuotient t α z/(t/2 : ℂ)^(2*z)

def bblrCentralGammaStrip (t A : ℝ) : Set ℂ := {z | |z.im|<t-A}

theorem bblrCentralGammaStrip_isOpen (t A : ℝ) : IsOpen (bblrCentralGammaStrip t A) :=
  isOpen_lt Complex.continuous_im.abs continuous_const

private theorem bblrCentralGammaArgument_im_ne_zero {t A : ℝ}
    (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A) {z : ℂ}
    (hz : z ∈ bblrCentralGammaStrip t A) (j : Fin 4) :
    ((sourceZetaPoints t j+α j+z)/2).im ≠ 0 := by
  have ha := abs_le.mp ((Complex.abs_im_le_norm (α j)).trans (hα j))
  have hzim := abs_lt.mp (show |z.im|<t-A from hz)
  fin_cases j <;> simp [sourceZetaPoints,criticalLinePoint] <;> simp at ha <;> linarith

private theorem bblrCentralGammaArgument_ne_neg_nat {t A : ℝ}
    (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A) {z : ℂ}
    (hz : z ∈ bblrCentralGammaStrip t A) (j : Fin 4) (n : ℕ) :
    (sourceZetaPoints t j+α j+z)/2 ≠ -(n : ℂ) := by
  intro he
  apply bblrCentralGammaArgument_im_ne_zero α hα hz j
  rw [he]
  simp

theorem bblrCentralNormalizedGamma_zero {t A : ℝ} (_hA : 0≤A) (ht : A<t)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A) :
    bblrCentralNormalizedGamma t α 0=1 := by
  have hz : (0 : ℂ) ∈ bblrCentralGammaStrip t A := by
    change |(0:ℂ).im|<t-A
    simpa using sub_pos.mpr ht
  have hg (j : Fin 4) : Gamma ((sourceZetaPoints t j+α j)/2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    simpa only [add_zero] using bblrCentralGammaArgument_ne_neg_nat α hα hz j
  simp [bblrCentralNormalizedGamma,bblrGammaQuotient,hg]

theorem bblrCentralNormalizedGamma_differentiableOn {t A : ℝ}
    (hA : 0≤A) (ht : A<t) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A) :
    DifferentiableOn ℂ (bblrCentralNormalizedGamma t α) (bblrCentralGammaStrip t A) := by
  have htpos : 0<t := hA.trans_lt ht
  have hb : (t/2 : ℂ) ≠ 0 := by
    exact div_ne_zero (Complex.ofReal_ne_zero.mpr htpos.ne') (by norm_num)
  have hQ : DifferentiableOn ℂ (bblrGammaQuotient t α) (bblrCentralGammaStrip t A) := by
    unfold bblrGammaQuotient
    apply DifferentiableOn.fun_finsetProd
    intro j _ z hz
    have ha : DifferentiableAt ℂ (fun z : ℂ => (sourceZetaPoints t j+α j+z)/2) z := by
      fun_prop
    exact (((Complex.differentiableAt_Gamma _
      (bblrCentralGammaArgument_ne_neg_nat α hα hz j)).comp z ha).div_const _).differentiableWithinAt
  have hP : DifferentiableOn ℂ (fun z : ℂ => (t/2 : ℂ)^(2*z))
      (bblrCentralGammaStrip t A) :=
    (differentiableOn_id.const_mul (2:ℂ)).const_cpow (.inl hb)
  exact hQ.div hP (fun z _ => by simp [hb])

theorem bblrCentralNormalizedGamma_analyticOnNhd {t A : ℝ}
    (hA : 0≤A) (ht : A<t) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A) :
    AnalyticOnNhd ℂ (bblrCentralNormalizedGamma t α) (bblrCentralGammaStrip t A) :=
  (bblrCentralNormalizedGamma_differentiableOn hA ht α hα).analyticOnNhd
    (bblrCentralGammaStrip_isOpen t A)

theorem bblrCentralNormalizedGamma_dslope_differentiableOn {t A : ℝ}
    (hA : 0≤A) (ht : A<t) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A) :
    DifferentiableOn ℂ (dslope (bblrCentralNormalizedGamma t α) 0)
      (bblrCentralGammaStrip t A) := by
  have hz : (0:ℂ) ∈ bblrCentralGammaStrip t A := by
    change |(0:ℂ).im|<t-A
    simpa using sub_pos.mpr ht
  exact (Complex.differentiableOn_dslope ((bblrCentralGammaStrip_isOpen t A).mem_nhds hz)).mpr
    (bblrCentralNormalizedGamma_differentiableOn hA ht α hα)

theorem bblrCentralNormalizedGamma_dslope_analyticOnNhd {t A : ℝ}
    (hA : 0≤A) (ht : A<t) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A) :
    AnalyticOnNhd ℂ (dslope (bblrCentralNormalizedGamma t α) 0)
      (bblrCentralGammaStrip t A) :=
  (bblrCentralNormalizedGamma_dslope_differentiableOn hA ht α hα).analyticOnNhd
    (bblrCentralGammaStrip_isOpen t A)

theorem bblrCentralNormalizedGamma_dslope_eq {t A : ℝ}
    (hA : 0≤A) (ht : A<t) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A)
    {z : ℂ} (hz : z≠0) :
    dslope (bblrCentralNormalizedGamma t α) 0 z=
      (bblrCentralNormalizedGamma t α z-1)/z := by
  rw [dslope_of_ne _ hz,slope_def_field,sub_zero,bblrCentralNormalizedGamma_zero hA ht α hα]

theorem bblrCentralGamma_ball_subset_strip {t A R : ℝ} (hR : R<t-A) :
    ball (0:ℂ) R ⊆ bblrCentralGammaStrip t A := by
  intro z hz
  have hn : ‖z‖<R := by simpa only [mem_ball,dist_zero_right] using hz
  exact (Complex.abs_im_le_norm z).trans_lt (hn.trans hR)

theorem bblrCentralNormalizedGamma_analyticOnNhd_ball {t A R : ℝ}
    (hA : 0≤A) (ht : A<t) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A) (hR : R<t-A) :
    AnalyticOnNhd ℂ (bblrCentralNormalizedGamma t α) (ball 0 R) :=
  (bblrCentralNormalizedGamma_analyticOnNhd hA ht α hα).mono
    (bblrCentralGamma_ball_subset_strip hR)

theorem bblrCentralNormalizedGamma_dslope_analyticOnNhd_ball {t A R : ℝ}
    (hA : 0≤A) (ht : A<t) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤A) (hR : R<t-A) :
    AnalyticOnNhd ℂ (dslope (bblrCentralNormalizedGamma t α) 0) (ball 0 R) :=
  (bblrCentralNormalizedGamma_dslope_analyticOnNhd hA ht α hα).mono
    (bblrCentralGamma_ball_subset_strip hR)

theorem bblrCentralNormalizedGamma_differentiableOn_rightHalfPlane {t : ℝ}
    (ht : 0<t) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
    DifferentiableOn ℂ (bblrCentralNormalizedGamma t α) {z : ℂ | 0<z.re} := by
  have hb : (t/2 : ℂ) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') (by norm_num)
  have hQ : DifferentiableOn ℂ (bblrGammaQuotient t α) {z : ℂ | 0<z.re} := by
    unfold bblrGammaQuotient
    apply DifferentiableOn.fun_finsetProd
    intro j _ z hz
    change 0<z.re at hz
    have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
    have hre : 0<((sourceZetaPoints t j+α j+z)/2).re := by
      fin_cases j <;> simp [sourceZetaPoints,criticalLinePoint] <;> simp at ha <;> norm_num at ha ⊢ <;> linarith
    have hn (n : ℕ) : (sourceZetaPoints t j+α j+z)/2 ≠ -(n:ℂ) := by
      intro he
      rw [he,neg_re,natCast_re] at hre
      have hn0 : (0:ℝ)≤n := Nat.cast_nonneg _
      linarith
    have haff : DifferentiableAt ℂ (fun z : ℂ => (sourceZetaPoints t j+α j+z)/2) z := by
      fun_prop
    exact (((Complex.differentiableAt_Gamma _ hn).comp z haff).div_const _).differentiableWithinAt
  have hP : DifferentiableOn ℂ (fun z : ℂ => (t/2 : ℂ)^(2*z)) {z : ℂ | 0<z.re} :=
    (differentiableOn_id.const_mul (2:ℂ)).const_cpow (.inl hb)
  exact hQ.div hP (fun z _ => by simp [hb])

theorem bblrCentralNormalizedGamma_analyticOnNhd_rightHalfPlane {t : ℝ}
    (ht : 0<t) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
    AnalyticOnNhd ℂ (bblrCentralNormalizedGamma t α) {z : ℂ | 0<z.re} :=
  (bblrCentralNormalizedGamma_differentiableOn_rightHalfPlane ht α hα).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

theorem bblrCentralNormalizedGamma_dslope_analyticOnNhd_rightHalfPlane {t : ℝ}
    (ht : 0<t) (α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
    AnalyticOnNhd ℂ (dslope (bblrCentralNormalizedGamma t α) 0) {z : ℂ | 0<z.re} := by
  have hd : DifferentiableOn ℂ (dslope (bblrCentralNormalizedGamma t α) 0)
      {z : ℂ | 0<z.re} :=
    (differentiableOn_dslope_of_notMem (by simp : (0:ℂ)∉{z : ℂ | 0<z.re})).mpr
      (bblrCentralNormalizedGamma_differentiableOn_rightHalfPlane ht α hα)
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

end
end SixthMoment.Source
