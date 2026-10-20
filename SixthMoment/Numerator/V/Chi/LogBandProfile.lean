import Mathlib.Analysis.MellinInversion
import SixthMoment.Analysis.Complex.PositivePowers
import SixthMoment.Analysis.Fourier.ProfileProduct
import SixthMoment.Analysis.Mellin.FourierCutoff
import SixthMoment.Analysis.Mellin.FourierScaling
import SixthMoment.Numerator.V.Chi.CosineScaling


namespace SixthMoment.Source
open Complex Real Set MeasureTheory Metric
open scoped ContDiff FourierTransform
noncomputable section

def noDPPositiveBandWindow (u : ℝ) : ℂ := (noDPFrequencyBump (8*(u-1)):ℂ)

theorem noDPPositiveBandWindow_contDiff : ContDiff ℝ ∞ noDPPositiveBandWindow :=
  Complex.ofRealCLM.contDiff.comp (noDPFrequencyBump.contDiff.comp (by fun_prop))

theorem noDPPositiveBandWindow_tsupport :
    tsupport noDPPositiveBandWindow ⊆ Icc (3/4:ℝ) (5/4) := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  have habs : |8*(u-1)| ≤ 2 := by
    by_contra hn
    have hbig : noDPFrequencyBump.rOut ≤ dist (8*(u-1)) (0:ℝ) := by
      simp only [noDPFrequencyBump,Real.dist_eq,sub_zero]
      exact le_of_lt (lt_of_not_ge hn)
    exact hu (by simp [noDPPositiveBandWindow,noDPFrequencyBump.zero_of_le_dist hbig])
  rw [abs_mul] at habs
  norm_num at habs
  have hsmall : |u-1| ≤ 1/4 := by linarith
  have H := abs_le.mp hsmall
  constructor <;> linarith

theorem noDPPositiveBandWindow_exp_one {v : ℝ} (hv : |v| ≤ 1/25) :
    noDPPositiveBandWindow (Real.exp v) = 1 := by
  have he := Real.abs_exp_sub_one_le (hv.trans (by norm_num : (1/25:ℝ) ≤ 1))
  have hb : 8*(Real.exp v-1) ∈ closedBall (0:ℝ) noDPFrequencyBump.rIn := by
    simp only [mem_closedBall,Real.dist_eq,sub_zero,noDPFrequencyBump,abs_mul]
    norm_num
    linarith
  simp [noDPPositiveBandWindow,noDPFrequencyBump.one_of_mem_closedBall hb]

def noDPLogBandProfile (h : SchwartzMap ℝ ℂ) (T c : ℝ) : ℝ → ℂ :=
  a03ProfileProduct noDPPositiveBandWindow (fun u =>
    ((T/(2*Real.pi):ℝ):ℂ)*(u:ℂ)^((c-1:ℝ):ℂ)*h (-T*Real.log u/(2*Real.pi))*
      (noDPFrequencyBump (-50*Real.log u):ℂ))

theorem noDPLogBandProfile_tsupport (h : SchwartzMap ℝ ℂ) (T c : ℝ) :
    tsupport (noDPLogBandProfile h T c) ⊆ Icc (3/4:ℝ) (5/4) :=
  (a03_profile_product_tsupport _ _).trans noDPPositiveBandWindow_tsupport

theorem noDPLogBandProfile_contDiff (h : SchwartzMap ℝ ℂ) (T c : ℝ) :
    ContDiff ℝ ∞ (noDPLogBandProfile h T c) := by
  apply a03_profile_product_contDiff noDPPositiveBandWindow_contDiff
  intro u hu
  have hu0 : 0 < u := by linarith [(noDPPositiveBandWindow_tsupport hu).1]
  have hlog : ContDiffAt ℝ ∞ Real.log u := Real.contDiffAt_log.mpr hu0.ne'
  have hx : ContDiffAt ℝ ∞ (fun x : ℝ => -T*Real.log x/(2*Real.pi)) u :=
    (contDiffAt_const.mul hlog).div_const _
  have hb : ContDiffAt ℝ ∞ (fun x : ℝ => (noDPFrequencyBump (-50*Real.log x):ℂ)) u :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp u
      (noDPFrequencyBump.contDiff.contDiffAt.comp u (contDiffAt_const.mul hlog))
  exact ((contDiffAt_const.mul (positive_cpow_contDiffAt ((c-1:ℝ):ℂ) hu0)).mul
    (h.smooth'.contDiffAt.comp u hx)).mul hb

theorem noDPLogBandProfile_log_pullback (h : SchwartzMap ℝ ℂ)
    {T : ℝ} (hT : 0 < T) (c x : ℝ) :
    (Real.exp (-(1-c)*x):ℂ)*noDPLogBandProfile h T c (Real.exp (-x)) =
      ((T/(2*Real.pi):ℝ):ℂ)*noDPFourierCutoff h (T/(100*Real.pi)) (T*x/(2*Real.pi)) := by
  have harg : (T*x/(2*Real.pi))/(T/(100*Real.pi)) = 50*x := by
    field_simp [hT.ne',Real.pi_ne_zero]
    ring
  have hpower : (Real.exp (-(1-c)*x):ℂ)*(Real.exp (-x):ℂ)^((c-1:ℝ):ℂ) = 1 := by
    rw [← Complex.ofReal_cpow (Real.exp_pos (-x)).le (c-1),← Complex.ofReal_mul,
      Real.rpow_def_of_pos (Real.exp_pos (-x)),Real.log_exp,← Real.exp_add,
      show -(1-c)*x+(-x)*(c-1) = 0 by ring,Real.exp_zero,Complex.ofReal_one]
  unfold noDPLogBandProfile a03ProfileProduct noDPFourierCutoff
  dsimp only
  rw [Real.log_exp,show -T*(-x)/(2*Real.pi) = T*x/(2*Real.pi) by ring,
    show -50*(-x) = 50*x by ring,harg]
  by_cases hz : noDPFrequencyBump (50*x) = 0
  · simp only [hz,Complex.ofReal_zero,mul_zero]
  · have hsmall : |x| ≤ 1/25 := by
      by_contra hn
      have hbig : noDPFrequencyBump.rOut ≤ dist (50*x) (0:ℝ) := by
        simp only [noDPFrequencyBump,Real.dist_eq,sub_zero,abs_mul]
        norm_num
        linarith [lt_of_not_ge hn]
      exact hz (noDPFrequencyBump.zero_of_le_dist hbig)
    rw [noDPPositiveBandWindow_exp_one (v := -x) (by simpa only [abs_neg] using hsmall),one_mul]
    calc
      _ = ((T/(2*Real.pi):ℝ):ℂ)*
          ((Real.exp (-(1-c)*x):ℂ)*(Real.exp (-x):ℂ)^((c-1:ℝ):ℂ))*
          h (T*x/(2*Real.pi))*(noDPFrequencyBump (50*x):ℂ) := by ring
      _ = _ := by rw [hpower]; ring

theorem noDPLogBandProfile_mellin (h : SchwartzMap ℝ ℂ)
    {T : ℝ} (hT : 0 < T) (c t : ℝ) :
    mellin (noDPLogBandProfile h T c) (1-((c:ℂ)+(t:ℂ)*I)) =
      𝓕⁻ (noDPFourierCutoff h (T/(100*Real.pi))) (t/T) := by
  have hp : 0 < T/(2*Real.pi) := by positivity
  rw [mellin_eq_fourier]
  simp only [sub_re,one_re,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero,
    sub_im,one_im,add_im,mul_I_im,zero_add,zero_sub,RCLike.real_smul_eq_coe_mul]
  have he : (fun x : ℝ => (Real.exp (-(1-c)*x):ℂ)*noDPLogBandProfile h T c (Real.exp (-x))) =
      fun x : ℝ => ((T/(2*Real.pi):ℝ):ℂ)*
        noDPFourierCutoff h (T/(100*Real.pi)) ((T/(2*Real.pi))*x) := by
    funext x
    rw [noDPLogBandProfile_log_pullback h hT c x]
    congr 2
    ring
  calc
    _ = 𝓕 (fun x : ℝ => ((T/(2*Real.pi):ℝ):ℂ)*
        noDPFourierCutoff h (T/(100*Real.pi)) ((T/(2*Real.pi))*x)) (-t/(2*Real.pi)) := by
      simpa only using! congrArg (fun f : ℝ → ℂ => 𝓕 f (-t/(2*Real.pi))) he
    _ = _ := by
      rw [fourier_positive_scale _ hp,fourierInv_eq_fourier_neg]
      field_simp [hT.ne',Real.pi_ne_zero]

theorem noDPLogBandProfile_chi_inverse (h : SchwartzMap ℝ ℂ)
    {T c r : ℝ} (hT : 0 < T) (hc : 0 < c) (hr : 0 < r) :
    (1/(2*Real.pi):ℂ)*(∫ t : ℝ,
      (r:ℂ)^(-((c:ℂ)+(t:ℂ)*I))*zetaChi (1-((c:ℂ)+(t:ℂ)*I))*
        𝓕⁻ (noDPFourierCutoff h (T/(100*Real.pi))) (t/T)) =
      2*a03SmoothedCosine (noDPLogBandProfile h T c) (2*Real.pi*r) := by
  have hs : tsupport (noDPLogBandProfile h T c) ⊆ Icc (3/4:ℝ) (2*(3/4)) := by
    intro u hu
    have H := noDPLogBandProfile_tsupport h T c hu
    exact ⟨H.1,by linarith [H.2]⟩
  have H := chi_cosine_inverse_mellin_positive_profile
    (noDPLogBandProfile_contDiff h T c) (by norm_num : (0:ℝ) < 3/4) hs hc hr
  unfold verticalIntegral at H
  simp_rw [noDPLogBandProfile_mellin h hT c] at H
  exact H

end
end SixthMoment.Source
