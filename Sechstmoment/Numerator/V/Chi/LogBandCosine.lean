import Sechstmoment.Numerator.V.Chi.BandPhase
import Sechstmoment.Numerator.V.Chi.LogBandProfile

/-! The actual positive cosine kernel in logarithmic frequency coordinates.
The changes of variables follow from the proved Mellin/Fourier identity. -/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped ContDiff FourierTransform
noncomputable section

theorem integral_positive_scale (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ, (a:ℂ)*f (a*x)) = ∫ x : ℝ, f x := by
  simpa [Real.fourier_eq'] using fourier_positive_scale f ha 0

theorem smoothed_cosine_eq_log_integral {g : ℝ → ℂ}
    (hg : Continuous g) (hK : HasCompactSupport g)
    (hs : tsupport g ⊆ Ioi (0:ℝ)) (freq : ℝ) :
    a03SmoothedCosine g freq = ∫ x : ℝ,
      (Real.exp (-x):ℂ)*((Real.cos (Real.exp (-x)*freq):ℂ)*g (Real.exp (-x))) := by
  let f : ℝ → ℂ := fun u => (Real.cos (u*freq):ℂ)*g u
  have hm : mellin f 1 = ∫ u : ℝ, f u := by
    unfold mellin
    simp only [sub_self,Complex.cpow_zero,one_smul]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro u hu
    have hz : g u = 0 := by
      apply Function.notMem_support.mp
      intro hn
      exact hu (hs (subset_tsupport g hn))
    simp only [f,hz,mul_zero]
  rw [a03SmoothedCosine_eq_time_integral hg hK]
  change (∫ u : ℝ, f u) = _
  rw [← hm]
  simpa [Real.fourier_eq',f,RCLike.real_smul_eq_coe_mul] using
    (mellin_eq_fourier f (s := (1:ℂ)))

theorem noDPLogBandProfile_cosine_integral (h : SchwartzMap ℝ ℂ)
    {T : ℝ} (hT : 0 < T) (c r : ℝ) :
    a03SmoothedCosine (noDPLogBandProfile h T c) (2*Real.pi*r) =
      ∫ ξ : ℝ, (Real.exp (c*((-2*Real.pi/T)*ξ)):ℂ)*
        noDPFourierCutoff h (T/(100*Real.pi)) ξ*
        (Real.cos (Real.exp ((-2*Real.pi/T)*ξ)*(2*Real.pi*r)):ℂ) := by
  let a := T/(2*Real.pi)
  let H := T/(100*Real.pi)
  let b := -2*Real.pi/T
  let F : ℝ → ℂ := fun ξ => (Real.exp (c*(b*ξ)):ℂ)*
    noDPFourierCutoff h H ξ*(Real.cos (Real.exp (b*ξ)*(2*Real.pi*r)):ℂ)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hS := noDPLogBandProfile_tsupport h T c
  have hK : HasCompactSupport (noDPLogBandProfile h T c) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hS
  have hs : tsupport (noDPLogBandProfile h T c) ⊆ Ioi (0:ℝ) := by
    intro u hu
    change 0 < u
    exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 3/4) (hS hu).1
  have hpull (x : ℝ) :
      (Real.exp (-(1-c)*x):ℂ)*noDPLogBandProfile h T c (Real.exp (-x)) =
        (a:ℂ)*noDPFourierCutoff h H (a*x) := by
    simpa only [a,H,div_mul_eq_mul_div] using
      noDPLogBandProfile_log_pullback h hT c x
  have he (x : ℝ) :
      (Real.exp (-x):ℂ)*noDPLogBandProfile h T c (Real.exp (-x)) =
        (Real.exp (-c*x):ℂ)*(a:ℂ)*noDPFourierCutoff h H (a*x) := by
    calc
      _ = (Real.exp (-c*x):ℂ)*
          ((Real.exp (-(1-c)*x):ℂ)*noDPLogBandProfile h T c (Real.exp (-x))) := by
        rw [← mul_assoc,← Complex.ofReal_mul,← Real.exp_add,
          show -c*x+(-(1-c)*x) = -x by ring]
      _ = _ := by rw [hpull]; ring
  have hb (x : ℝ) : b*(a*x) = -x := by
    dsimp only [a,b]
    field_simp [hT.ne',Real.pi_ne_zero]
  rw [smoothed_cosine_eq_log_integral
    (noDPLogBandProfile_contDiff h T c).continuous hK hs]
  calc
    _ = ∫ x : ℝ, (a:ℂ)*F (a*x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [F]
      rw [hb]
      rw [show c*(-x) = -c*x by ring]
      have Hpoint := he x
      linear_combination (Real.cos (Real.exp (-x)*(2*Real.pi*r)):ℂ)*Hpoint
    _ = ∫ ξ : ℝ, F ξ := integral_positive_scale F ha
    _ = _ := rfl

theorem noDPLogBandProfile_two_cosine_eq_bands (h : SchwartzMap ℝ ℂ)
    {T : ℝ} (hT : 0 < T) (c r : ℝ) :
    2*a03SmoothedCosine (noDPLogBandProfile h T c) (2*Real.pi*r) =
      (∫ ξ : ℝ, noDPBandPhaseIntegrand h (T/(100*Real.pi))
        (2*Real.pi*r) c (-2*Real.pi/T) ξ)+
      (∫ ξ : ℝ, noDPBandPhaseIntegrand h (T/(100*Real.pi))
        (-2*Real.pi*r) c (-2*Real.pi/T) ξ) := by
  have hH : 0 < T/(100*Real.pi) := by positivity
  rw [noDPLogBandProfile_cosine_integral h hT c r,← integral_const_mul,
    ← integral_add (noDPBandPhase_integrable h hH (2*Real.pi*r) c (-2*Real.pi/T))
      (noDPBandPhase_integrable h hH (-2*Real.pi*r) c (-2*Real.pi/T))]
  apply integral_congr_ae
  filter_upwards [] with ξ
  let θ : ℂ := (Real.exp ((-2*Real.pi/T)*ξ)*(2*Real.pi*r):ℝ)
  have hp : I*(((2*Real.pi*r)*Real.exp ((-2*Real.pi/T)*ξ):ℝ):ℂ) = θ*I := by
    dsimp only [θ]
    push_cast
    ring
  have hn : I*(((-2*Real.pi*r)*Real.exp ((-2*Real.pi/T)*ξ):ℝ):ℂ) = -θ*I := by
    dsimp only [θ]
    push_cast
    ring
  unfold noDPBandPhaseIntegrand
  rw [hp,hn,Complex.ofReal_cos]
  change 2*((Real.exp (c*((-2*Real.pi/T)*ξ)):ℂ)*
    noDPFourierCutoff h (T/(100*Real.pi)) ξ*Complex.cos θ) = _
  rw [Complex.cos]
  ring

def noDPChiBandTransform (h : SchwartzMap ℝ ℂ) (T c r : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*(∫ t : ℝ,
    (r:ℂ)^(-((c:ℂ)+(t:ℂ)*I))*zetaChi (1-((c:ℂ)+(t:ℂ)*I))*
      𝓕⁻ (noDPFourierCutoff h (T/(100*Real.pi))) (t/T))

theorem noDPChiBandTransform_eq_bands (h : SchwartzMap ℝ ℂ)
    {T c r : ℝ} (hT : 0 < T) (hc : 0 < c) (hr : 0 < r) :
    noDPChiBandTransform h T c r =
      (∫ ξ : ℝ, noDPBandPhaseIntegrand h (T/(100*Real.pi))
        (2*Real.pi*r) c (-2*Real.pi/T) ξ)+
      (∫ ξ : ℝ, noDPBandPhaseIntegrand h (T/(100*Real.pi))
        (-2*Real.pi*r) c (-2*Real.pi/T) ξ) := by
  unfold noDPChiBandTransform
  rw [noDPLogBandProfile_chi_inverse h hT hc hr,
    noDPLogBandProfile_two_cosine_eq_bands h hT c r]

end
end Sechstmoment.Source
