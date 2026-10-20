import Sechstmoment.Analysis.Complex.RealDerivatives
import Sechstmoment.Zeta.Centering.PhaseComplex


namespace Sechstmoment
open Complex Filter Metric Asymptotics
open scoped Topology
noncomputable section

def centeringUniformConstant (R : ℝ) : ℝ :=
  768*(R+R^2)+2*R*centeringPhaseComplexBound

private theorem normalizedGammaRatio_height_bound (s v : ℂ) {T R : ℝ}
    (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) (hre : -|s.im| ≤ s.re)
    (him : T/4 ≤ |s.im|) (hT : 192*(R+R^2)+8 ≤ T) :
    ‖normalizedGammaRatio s v-1‖ ≤ 96*(R+R^2)/T := by
  have hM : 0 ≤ R+R^2 := by positivity
  have hT0 : 0 < T := by linarith
  have him2 : 2 ≤ |s.im| := by linarith
  have him0 : 0 < |s.im| := by linarith
  have hN : ‖v‖+‖v‖^2 ≤ R+R^2 := by nlinarith [norm_nonneg v]
  have hlarge : 24*(‖v‖+‖v‖^2) < |s.im| := by linarith
  have hgamma := gammaRatio_normalized_error_cone s v hre him2 hlarge
  change ‖normalizedGammaRatio s v-1‖ ≤ _ at hgamma
  apply hgamma.trans
  calc
    _ ≤ 24*(R+R^2)/|s.im| := div_le_div_of_nonneg_right (by linarith) him0.le
    _ ≤ 24*(R+R^2)/(T/4) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) him
    _ = _ := by ring

theorem centeringFactorAt_complex_height_bound {T R : ℝ} {x z : ℂ}
    (hxre : x.re ∈ Set.Icc (3/4 : ℝ) (9/4)) (hxim : |x.im| ≤ 1/4)
    (hz : ‖z‖ ≤ R) (hL : 1 ≤ Real.log T)
    (hT : 192*(R+R^2)+8 ≤ T)
    (hlarge : 2*R*centeringPhaseComplexBound ≤ Real.log T) :
    ‖centeringFactorAt T (complexHeightPoint T x) z-1‖ ≤
      centeringUniformConstant R/Real.log T := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hz
  have hM : 0 ≤ R+R^2 := by positivity
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  have hc := gammaHeight_mem_cone hT0.le hxre.1 hxim
  have hi := gammaHeight_im_abs_lower hT0.le hxre.1
  have hv : ‖(z/(Real.log T : ℂ))/2‖ ≤ R := by
    rw [norm_div, Complex.norm_ofNat, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hL0]
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    apply (div_le_iff₀ hL0).mpr
    nlinarith
  have hv' : ‖-(z/(Real.log T : ℂ))/2‖ ≤ R := by
    simpa only [neg_div, norm_neg] using hv
  have hA := normalizedGammaRatio_height_bound (gammaHeightA T x)
    (-(z/(Real.log T : ℂ))/2) hR hv' hc.1 (by linarith [hi.1]) hT
  have hB := normalizedGammaRatio_height_bound (gammaHeightB T x)
    ((z/(Real.log T : ℂ))/2) hR hv hc.2 (by linarith [hi.2]) hT
  have hδ : 0 ≤ 96*(R+R^2)/T := by positivity
  have hδsmall : 96*(R+R^2)/T ≤ 1/2 :=
    (div_le_iff₀ hT0).mpr (by linarith)
  have hpoint : 3*T/4 ≤ |(complexHeightPoint T x).im| := by
    have he : |(complexHeightPoint T x).im| = 2*|(gammaHeightB T x).im| := by
      simp only [gammaHeightB, Complex.div_ofNat_im, abs_div]
      norm_num
      ring
    rw [he]
    linarith [hi.2]
  have hs : (complexHeightPoint T x).im ≠ 0 := by
    intro h
    simp only [h, abs_zero] at hpoint
    linarith
  have hw : (complexHeightPoint T x+z/(Real.log T : ℂ)).im ≠ 0 := by
    intro h
    have he : (complexHeightPoint T x).im = -(z/(Real.log T : ℂ)).im := by
      simp only [Complex.add_im] at h
      linarith
    have hu : ‖z/(Real.log T : ℂ)‖ ≤ R := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0,
        div_le_iff₀ hL0]
      nlinarith
    have him := Complex.abs_im_le_norm (z/(Real.log T : ℂ))
    rw [he, abs_neg] at hpoint
    nlinarith [sq_nonneg R]
  have hp := centeringGammaMain_error_bound hT1 hxre hxim hz hL0 (by
    have hk := centeringPhaseComplexBound_pos
    nlinarith)
  have hp' : ‖gammaChiMainPhase (complexHeightPoint T x)
      (z/(Real.log T : ℂ)) z-1‖ ≤ 2*R*centeringPhaseComplexBound/Real.log T := by
    simpa only [centeringGammaMain_eq_gammaChiMainPhase] using hp
  have hE : 2*R*centeringPhaseComplexBound/Real.log T ≤ 1 :=
    (div_le_one hL0).mpr hlarge
  have hactual := centeringFactorAt_error_bound T (complexHeightPoint T x) z hs hw
    hδ hδsmall hE hA hB hp'
  apply hactual.trans
  have hlogT : Real.log T ≤ T := Real.log_le_self hT0.le
  calc
    _ ≤ 8*(96*(R+R^2)/Real.log T)+2*R*centeringPhaseComplexBound/Real.log T := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (by positivity) hL0 hlogT) (by norm_num)) le_rfl
    _ = _ := by unfold centeringUniformConstant; ring

theorem centeringFactorAt_uniform_complex_height_bound (R : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ x z : ℂ,
      x.re ∈ Set.Icc (3/4 : ℝ) (9/4) → |x.im| ≤ 1/4 → ‖z‖ ≤ R →
      ‖centeringFactorAt T (complexHeightPoint T x) z-1‖ ≤
        centeringUniformConstant R/Real.log T := by
  have hlog := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (2*R*centeringPhaseComplexBound)))
  filter_upwards [hlog, eventually_ge_atTop (192*(R+R^2)+8)] with T hLT hT
  intro x z hxre hxim hz
  exact centeringFactorAt_complex_height_bound hxre hxim hz
    ((le_max_left _ _).trans hLT) hT ((le_max_right _ _).trans hLT)

theorem centeringFactor_uniform_disk_bound (R : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ x : ℝ, x ∈ Set.Icc (1 : ℝ) 2 →
      ∀ z : ℂ, ‖z‖ ≤ R →
        ‖centeringFactor T (T*x) z-1‖ ≤ centeringUniformConstant R/Real.log T := by
  filter_upwards [centeringFactorAt_uniform_complex_height_bound R] with T hT
  intro x hx z hz
  have hp : complexHeightPoint T (x : ℂ) = criticalLinePoint (T*x) := by
    unfold complexHeightPoint criticalLinePoint
    push_cast
    ring
  have h := hT (x : ℂ) z (by simp only [Complex.ofReal_re]; constructor <;> linarith [hx.1,hx.2])
    (by simp) hz
  rw [hp, centeringFactorAt_criticalLinePoint] at h
  exact h

theorem complexHeightPoint_shift_nonreal {T R : ℝ} {x z : ℂ}
    (hxre : 3/4 ≤ x.re) (hz : ‖z‖ ≤ R) (hL : 1 ≤ Real.log T)
    (hT : 192*(R+R^2)+8 ≤ T) :
    (complexHeightPoint T x).im ≠ 0 ∧
      (complexHeightPoint T x+z/(Real.log T : ℂ)).im ≠ 0 := by
  have hR : 0 ≤ R := (norm_nonneg _).trans hz
  have hM : 0 ≤ R+R^2 := by positivity
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  have hp : (complexHeightPoint T x).im = T*x.re := by
    simp [complexHeightPoint, Complex.mul_im]
  have hu : ‖z/(Real.log T : ℂ)‖ ≤ R := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0,
      div_le_iff₀ hL0]
    nlinarith
  have hul : -R ≤ (z/(Real.log T : ℂ)).im := by
    have hb := (Complex.abs_im_le_norm (z/(Real.log T : ℂ))).trans hu
    exact (abs_le.mp hb).1
  have hprod := mul_le_mul_of_nonneg_left hxre hT0.le
  constructor
  · rw [hp]
    exact ne_of_gt (by nlinarith)
  · simp only [Complex.add_im, hp]
    exact ne_of_gt (by nlinarith [sq_nonneg R])

private theorem closedBall_real_quarter_height_window {x : ℝ}
    (hx : x ∈ Set.Icc (1 : ℝ) 2) {y : ℂ} (hy : y ∈ closedBall (x : ℂ) (1/4 : ℝ)) :
    y.re ∈ Set.Icc (3/4 : ℝ) (9/4) ∧ |y.im| ≤ 1/4 := by
  have hn : ‖y-(x : ℂ)‖ ≤ 1/4 := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have hre := (Complex.abs_re_le_norm (y-(x : ℂ))).trans hn
  have him := (Complex.abs_im_le_norm (y-(x : ℂ))).trans hn
  simp only [Complex.sub_re, Complex.ofReal_re] at hre
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
  exact ⟨⟨by linarith [(abs_le.mp hre).1, hx.1],
    by linarith [(abs_le.mp hre).2, hx.2]⟩, him⟩

theorem centeringFactor_uniform_real_derivative_bound (n : ℕ) (R : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ x : ℝ, x ∈ Set.Icc (1 : ℝ) 2 →
      ∀ z : ℂ, ‖z‖ ≤ R →
        ‖iteratedDeriv n (fun y : ℝ => centeringFactor T (T*y) z-1) x‖ ≤
          ((Nat.factorial n : ℝ)/(1/4 : ℝ)^n)*
            (centeringUniformConstant R/Real.log T) := by
  have hlog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [centeringFactorAt_uniform_complex_height_bound R, hlog,
    eventually_ge_atTop (192*(R+R^2)+8)] with T hbound hL hT
  intro x hx z hz
  let f : ℂ → ℂ := fun y => centeringFactorAt T (complexHeightPoint T y) z-1
  have ha : AnalyticOnNhd ℂ f (closedBall (x : ℂ) (1/4 : ℝ)) := by
    intro y hy
    have hwindow := closedBall_real_quarter_height_window hx hy
    have hnonreal := complexHeightPoint_shift_nonreal hwindow.1.1 hz hL hT
    exact centeringFactorAt_error_analyticAt_height T z hnonreal.1 hnonreal.2
  have hf : DiffContOnCl ℂ f (ball (x : ℂ) (1/4 : ℝ)) :=
    (ha.differentiableOn.mono closure_ball_subset_closedBall).diffContOnCl
  have hM (y : ℂ) (hy : y ∈ sphere (x : ℂ) (1/4 : ℝ)) :
      ‖f y‖ ≤ centeringUniformConstant R/Real.log T := by
    have hwindow := closedBall_real_quarter_height_window hx (sphere_subset_closedBall hy)
    exact hbound y z hwindow.1 hwindow.2 hz
  have he : (fun y : ℝ => f (y : ℂ)) =
      (fun y : ℝ => centeringFactor T (T*y) z-1) := by
    funext y
    have hp : complexHeightPoint T (y : ℂ) = criticalLinePoint (T*y) := by
      unfold complexHeightPoint criticalLinePoint
      push_cast
      ring
    simp only [f, hp, centeringFactorAt_criticalLinePoint]
  rw [← he]
  exact cauchy_real_iteratedDeriv_bound n (by norm_num) hf hM

theorem centeringError_real_derivative_invLog_isBigO (n : ℕ) (R : ℝ)
    (x : ℝ → ℝ) (z : ℝ → ℂ)
    (hx : ∀ᶠ T in atTop, x T ∈ Set.Icc (1 : ℝ) 2)
    (hz : ∀ᶠ T in atTop, ‖z T‖ ≤ R) :
    (fun T => iteratedDeriv n (fun y : ℝ => centeringFactor T (T*y) (z T)-1) (x T))
      =O[atTop] (fun T => (Real.log T)⁻¹) := by
  apply IsBigO.of_bound (((Nat.factorial n : ℝ)/(1/4 : ℝ)^n)*centeringUniformConstant R)
  filter_upwards [centeringFactor_uniform_real_derivative_bound n R, hx, hz,
    eventually_gt_atTop (1 : ℝ)] with T hbound hTx hTz hT
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.log_pos hT).le)]
  simpa only [div_eq_mul_inv, mul_assoc] using hbound (x T) hTx (z T) hTz

end
end Sechstmoment
