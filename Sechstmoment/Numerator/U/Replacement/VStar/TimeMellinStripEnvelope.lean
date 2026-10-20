import Sechstmoment.Numerator.U.Replacement.VStar.TimeMellinRepresentation
import Sechstmoment.Numerator.U.ZeroModes.RatioLeadingBranchSmooth

namespace Sechstmoment
open Complex Real Source Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 700000

theorem a03VStarSmoothedTimeMellin_strip_full_height_envelope {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (A B : ℝ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,∀ σ : MomentShifts,∀ Y x : ℝ,0<Y → 0<x →
      ∀ s : ℂ,s.re∈Icc A B →
      (1+|s.im|)^N*‖a03VStarSmoothedTimeMellin Φ T σ Y x s‖≤
        C*(1+polarGaussianConstant T σ 1)*a03ZeroModeRatioXEnvelope Y x := by
  obtain ⟨Cp,hCp,hpos⟩ := a03GaussianPositiveTimeMellinIntegral_strip_full_height_decay hΦ hSupp (3-B) (3-A) 2 N
  obtain ⟨Cn,hCn,hneg⟩ := a03GaussianPositiveTimeMellinIntegral_strip_full_height_decay hΦ hSupp (-1-B) (-1-A) (-2) N
  obtain ⟨C₀,hC₀,hplain⟩ := a03PositiveTimeMellin_strip_full_height_decay hΦ hSupp (1-B) (1-A) N
  let P : ℝ := (2*Real.pi)^2
  have hP : 0<P := by dsimp [P]; positivity
  let C : ℝ := C₀+P*Cn+Cp/P
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro T σ Y x hY hx s hsc
  have hCG := polarGaussianConstant_nonneg T σ 1
  have hheight : 0≤(1+|s.im|)^N := by positivity
  have hbase : 0<(2*Real.pi)^2*x^2/Y^2 := by positivity
  have hexp : Real.exp (a03VStarSpatialLog Y x)=P*(x/Y)^2 := by
    unfold a03VStarSpatialLog
    rw [Real.exp_log hbase]
    dsimp only [P]
    ring
  have hplainarg : (1:ℂ)-s=((1-s.re:ℝ):ℂ)+((-s.im:ℝ):ℂ)*I := by
    apply Complex.ext <;> simp
  have hpl := hplain (1-s.re) ⟨by linarith [hsc.2],by linarith [hsc.1]⟩ (-s.im)
  have hn := hneg T σ (-a03VStarSpatialLog Y x) (-1-s.re)
    ⟨by linarith [hsc.2],by linarith [hsc.1]⟩ (-s.im)
  have hp := hpos T σ (a03VStarSpatialLog Y x) (3-s.re)
    ⟨by linarith [hsc.2],by linarith [hsc.1]⟩ (-s.im)
  simp only [abs_neg,neg_neg] at hpl hn hp
  by_cases hxy : x≤Y
  · rw [a03ZeroModeRatioXEnvelope_near hx hxy,mul_one]
    have he : Real.exp (a03VStarSpatialLog Y x)≤P := by
      rw [hexp]
      have hd : 0≤x/Y := div_nonneg hx.le hY.le
      have hd1 : x/Y≤1 := (div_le_iff₀ hY).mpr (by simpa using hxy)
      have hs : (x/Y)^2≤1 := by nlinarith only [hd,hd1]
      exact (mul_le_mul_of_nonneg_left hs hP.le).trans_eq (mul_one _)
    rw [a03VStarSmoothedTimeMellin_eq_reflected hΦ.continuous hSupp hY hx T σ s]
    calc
      _≤(1+|s.im|)^N*(‖mellin Φ (1-s)‖+
        ‖a03GaussianPositiveTimeMellinIntegral Φ T σ (-a03VStarSpatialLog Y x) (-1-s.re) (-2) (-s.im)‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) hheight
      _≤C₀+Cn*polarGaussianConstant T σ 1*P := by
        rw [mul_add]
        exact add_le_add (by simpa only [hplainarg] using hpl) (hn.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hCn hCG)))
      _≤_ := by dsimp only [C]; nlinarith only [hC₀,hCn,hCp,hCG,hP,div_nonneg hCp hP.le]
  · have hxy' : Y<x := lt_of_not_ge hxy
    rw [a03ZeroModeRatioXEnvelope_far hY.le hxy']
    have he : Real.exp (-a03VStarSpatialLog Y x)=(Y/x)^2/P := by
      rw [Real.exp_neg,hexp]
      dsimp only [P]
      field_simp
    rw [a03VStarSmoothedTimeMellin_eq_positive hΦ.continuous hSupp hY hx T σ s]
    calc
      _≤Cp*polarGaussianConstant T σ 1*Real.exp (-a03VStarSpatialLog Y x) := hp
      _=(Cp/P)*polarGaussianConstant T σ 1*(Y/x)^2 := by rw [he]; ring
      _≤_ := by
        have hcoef : Cp/P≤C := by dsimp only [C]; linarith only [hC₀,mul_nonneg hP.le hCn]
        have hh : (Cp/P)*polarGaussianConstant T σ 1≤C*(1+polarGaussianConstant T σ 1) := by
          exact (mul_le_mul_of_nonneg_right hcoef hCG).trans
            (mul_le_mul_of_nonneg_left (by linarith only [] : polarGaussianConstant T σ 1≤1+polarGaussianConstant T σ 1) hC)
        exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)


theorem a03VStarSmoothedTimeMellin_power_profile_eq {Φ : ℝ→ℂ}
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (T : ℝ) (σ : MomentShifts)
    (Y x : ℝ) (ρ s : ℂ) :
    a03VStarSmoothedTimeMellin (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^ρ)) T σ Y x s=
      a03VStarSmoothedTimeMellin Φ T σ Y x (s-ρ) := by
  unfold a03VStarSmoothedTimeMellin a03ProfileProduct
  apply integral_congr_ae
  apply ae_of_all
  intro t
  by_cases ht : Φ t=0
  · simp only [ht,zero_mul]
  · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
    have ht0 : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr htp.ne'
    calc
      _=(Φ t*bblrVStar (polarPoleKiller T σ) (x^2/(Y^2*t^2)))*((t:ℂ)^ρ*(t:ℂ)^(-s)) := by ring
      _=_ := by rw [←Complex.cpow_add ρ (-s) ht0]; congr 2; ring

theorem a03VStarSmoothedTimeMellin_power_full_height_envelope {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (cs : ℝ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ ρ : ℂ,‖ρ‖≤1 → ∀ T : ℝ,∀ σ : MomentShifts,
      ∀ Y x : ℝ,0<Y → 0<x → ∀ s : ℂ,s.re=cs →
      (1+|s.im|)^N*‖a03VStarSmoothedTimeMellin
        (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^ρ)) T σ Y x s‖≤
        C*(1+polarGaussianConstant T σ 1)*a03ZeroModeRatioXEnvelope Y x := by
  obtain ⟨D,hD,hstrip⟩ := a03VStarSmoothedTimeMellin_strip_full_height_envelope hΦ hSupp (cs-1) (cs+1) N
  refine ⟨2^N*D,by positivity,?_⟩
  intro ρ hρ T σ Y x hY hx s hsc
  have hρre := (Complex.abs_re_le_norm ρ).trans hρ
  have hρim := (Complex.abs_im_le_norm ρ).trans hρ
  have hr : (s-ρ).re∈Icc (cs-1) (cs+1) := by
    simp only [Complex.sub_re,hsc]
    constructor <;> linarith [(abs_le.mp hρre).1,(abs_le.mp hρre).2]
  have hh : 1+|s.im|≤2*(1+|(s-ρ).im|) := by
    have ht : |s.im|≤|s.im-ρ.im|+|ρ.im| := by
      simpa only [sub_add_cancel] using abs_add_le (s.im-ρ.im) ρ.im
    rw [Complex.sub_im]
    linarith [abs_nonneg (s.im-ρ.im)]
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1+|s.im|) hh N
  rw [mul_pow] at hp
  rw [a03VStarSmoothedTimeMellin_power_profile_eq hSupp]
  calc
    _≤2^N*((1+|(s-ρ).im|)^N*‖a03VStarSmoothedTimeMellin Φ T σ Y x (s-ρ)‖) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _≤2^N*(D*(1+polarGaussianConstant T σ 1)*a03ZeroModeRatioXEnvelope Y x) :=
      mul_le_mul_of_nonneg_left (hstrip T σ Y x hY hx (s-ρ) hr) (by positivity)
    _=_ := by ring

theorem a03VStarSmoothedTimeMellin_actual_branch_full_height_envelope {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    (K : Set MomentShifts) (hK : IsCompact K) (cs : ℝ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ dual : Bool,
      ∀ Y x : ℝ,0<Y → 0<x → ∀ s : ℂ,s.re=cs →
      (1+|s.im|)^N*‖a03VStarSmoothedTimeMellin
        (a03RatioLeadingBranchProfile dual Φ T σ) T σ Y x s‖≤
        C*(1+polarGaussianConstant T σ 1)*a03ZeroModeRatioXEnvelope Y x := by
  obtain ⟨D,hD,hbound⟩ := a03VStarSmoothedTimeMellin_power_full_height_envelope hΦ hSupp cs N
  obtain ⟨E,hE,hscalar⟩ := a03RatioLeadingScalar_uniform_eventually_bound K hK
  refine ⟨E*D,by positivity,?_⟩
  filter_upwards [hscalar,a03RatioLeadingExponent_uniform_eventually_small K hK,eventually_gt_atTop (0:ℝ)]
    with T hs hr hT
  intro σ hσ dual Y x hY hx s hsc
  have he : a03VStarSmoothedTimeMellin (a03RatioLeadingBranchProfile dual Φ T σ) T σ Y x s=
      a03RatioLeadingScalar dual T σ*a03VStarSmoothedTimeMellin
        (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^(a03RatioLeadingExponent dual T σ))) T σ Y x s := by
    rw [a03RatioLeadingBranchProfile_eq_scalar_power hSupp hT σ dual]
    unfold a03VStarSmoothedTimeMellin
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun t => by ring
  rw [he,norm_mul]
  have hb := hbound (a03RatioLeadingExponent dual T σ) (hr σ hσ dual) T σ Y x hY hx s hsc
  calc
    _=‖a03RatioLeadingScalar dual T σ‖*((1+|s.im|)^N*‖a03VStarSmoothedTimeMellin
      (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^(a03RatioLeadingExponent dual T σ))) T σ Y x s‖) := by ring
    _≤E*(D*(1+polarGaussianConstant T σ 1)*a03ZeroModeRatioXEnvelope Y x) :=
      mul_le_mul (hs σ hσ dual) hb (by positivity) hE
    _=_ := by ring

end
end Sechstmoment
