import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# The genuine profile inversion used in §3.1

Smooth compactly supported profiles are converted into Schwartz functions after
exponential weighting. Their bilateral Laplace transforms on vertical lines
are actual Fourier transforms, so inversion and rapid decay follow from the
proved Schwartz Fourier theory. No contour estimate for zeta is assumed here.
-/

namespace Sechstmoment

open Real Complex MeasureTheory
open scoped FourierTransform ContDiff SchwartzMap

noncomputable section

/-- The profile transform `F_f(w)` of §3.1. -/
def profileLaplaceTransform (f : ℝ → ℂ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (w * x) * f x

def profileExponentialWeight (f : ℝ → ℂ) (c : ℝ) (x : ℝ) : ℂ :=
  (Real.exp (c*x) : ℂ) * f x

theorem profileExponentialWeight_hasCompactSupport {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (c : ℝ) :
    HasCompactSupport (profileExponentialWeight f c) :=
  hf.mul_left

theorem profileExponentialWeight_contDiff {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (c : ℝ) :
    ContDiff ℝ ∞ (profileExponentialWeight f c) := by
  unfold profileExponentialWeight
  apply ContDiff.mul _ hf
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))

/-- Exponential weighting preserves the concrete compactly supported smooth
profile; its associated Schwartz map has this same underlying function. -/
def profileWeightedSchwartz (f : ℝ → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (c : ℝ) : 𝓢(ℝ, ℂ) :=
  (profileExponentialWeight_hasCompactSupport hf c).toSchwartzMap
    (profileExponentialWeight_contDiff hs c)

@[simp] theorem profileWeightedSchwartz_coe (f : ℝ → ℂ) (hf : HasCompactSupport f)
    (hs : ContDiff ℝ ∞ f) (c : ℝ) :
    (profileWeightedSchwartz f hf hs c : ℝ → ℂ) = profileExponentialWeight f c := rfl

/-- The vertical-line profile transform is a Fourier transform with the actual
frequency and sign used by the manuscript. -/
theorem profileLaplaceTransform_eq_fourier (f : ℝ → ℂ) (c v : ℝ) :
    profileLaplaceTransform f (c + v*I) =
      𝓕 (profileExponentialWeight f c) (-v/(2*π)) := by
  rw [profileLaplaceTransform, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  rw [profileExponentialWeight, smul_eq_mul, ← mul_assoc, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat]
  field_simp
  ring

/-- Integrability on every vertical line is proved from compact support and
smoothness, rather than added as an inversion hypothesis. -/
theorem profileLaplaceTransform_verticalIntegrable {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) (c : ℝ) :
    VerticalIntegrable (profileLaplaceTransform f) c := by
  let g := profileWeightedSchwartz f hf hs c
  have hg : Integrable (𝓕 (profileExponentialWeight f c)) := (𝓕 g).integrable
  have ha : -1/(2*π) ≠ 0 := by positivity
  have hi := hg.comp_mul_left' ha
  change Integrable (fun v : ℝ => profileLaplaceTransform f (c + v*I))
  convert hi using 1
  funext v
  rw [profileLaplaceTransform_eq_fourier]
  exact congrArg (𝓕 (profileExponentialWeight f c)) (by ring)

/-- Arbitrary-order rapid decay on a fixed vertical line, with an explicit
Schwartz-seminorm bound at the correctly normalized frequency. -/
theorem profileLaplaceTransform_vertical_decay {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) (c : ℝ) (k : ℕ) :
    ∃ C : ℝ, ∀ v : ℝ,
      (1+|-v/(2*π)|)^k * ‖profileLaplaceTransform f (c+v*I)‖ ≤ C := by
  let g := profileWeightedSchwartz f hf hs c
  refine ⟨2^k * (Finset.Iic (k, 0)).sup
      (fun m => SchwartzMap.seminorm ℂ m.1 m.2) (𝓕 g), ?_⟩
  intro v
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (k,0)) (k := k) (n := 0) le_rfl le_rfl (𝓕 g) (-v/(2*π))
  simpa [profileLaplaceTransform_eq_fourier, SchwartzMap.fourier_coe,
    Real.norm_eq_abs, g, abs_div] using h

/-- Actual bilateral Laplace inversion for each smooth compactly supported
profile. The contour is parameterized by `c + v*i`, hence its prefactor is
`1/(2*pi)`. -/
theorem profileLaplaceTransform_inversion {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f) (c y : ℝ) :
    f y = (1/(2*π):ℂ) * ∫ v : ℝ,
      Complex.exp (-(c+v*I)*(y:ℂ)) * profileLaplaceTransform f (c+v*I) := by
  let g := profileWeightedSchwartz f hf hs c
  have hinv : 𝓕⁻ (𝓕 (profileExponentialWeight f c)) y =
      profileExponentialWeight f c y :=
    congrFun (g.continuous.fourierInv_fourier_eq g.integrable (𝓕 g).integrable) y
  rw [Real.fourierInv_eq'] at hinv
  have hscale := Measure.integral_comp_mul_left (fun v : ℝ =>
      Complex.exp (-(c+v*I)*(y:ℂ)) * profileLaplaceTransform f (c+v*I))
    (-2*π)
  have hweight : ∫ v : ℝ,
      Complex.exp (-((c:ℂ)+((-2*π*v:ℝ):ℂ)*I)*(y:ℂ)) *
        profileLaplaceTransform f ((c:ℂ)+((-2*π*v:ℝ):ℂ)*I) =
      Complex.exp (-(c:ℂ)*y) * ∫ v : ℝ,
        Complex.exp ((↑(2*π*inner ℝ v y))*I) •
          (𝓕 (profileExponentialWeight f c)) v := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [profileLaplaceTransform_eq_fourier]
    have hv : -(-2*π*v)/(2*π) = v := by field_simp
    rw [hv, smul_eq_mul, ← mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring
  rw [hweight, hinv, profileExponentialWeight, Complex.ofReal_exp,
    ← mul_assoc, ← Complex.exp_add] at hscale
  have hcancel : -(c:ℂ)*y + ↑(c*y) = 0 := by push_cast; ring
  rw [hcancel, Complex.exp_zero, one_mul] at hscale
  have ha : |(-2*π)⁻¹| = (2*π)⁻¹ := by
    rw [abs_inv, abs_of_neg (by nlinarith [pi_pos])]
    congr 1
    ring
  simpa only [ha, real_smul, one_div, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat] using hscale

/-- Rescaled inversion with the exact `L/(2*pi)` factor, parameterizing the
manuscript's contour `Re u = δ` by `u = δ + t*i`. -/
theorem profileLaplaceTransform_scaled_inversion {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f)
    {L : ℝ} (hL : 0 < L) (δ y : ℝ) :
    f y = ((L:ℂ)/(2*π)) * ∫ t : ℝ,
      Complex.exp (-((L:ℂ)*((δ:ℂ)+t*I))*(y:ℂ)) *
        profileLaplaceTransform f ((L:ℂ)*((δ:ℂ)+t*I)) := by
  have hw (t : ℝ) : (L:ℂ)*((δ:ℂ)+t*I) =
      ((L*δ:ℝ):ℂ)+((L*t:ℝ):ℂ)*I := by push_cast; ring
  have hscale := Measure.integral_comp_mul_left (fun v : ℝ =>
      Complex.exp (-(((L*δ:ℝ):ℂ)+v*I)*(y:ℂ)) *
        profileLaplaceTransform f (((L*δ:ℝ):ℂ)+v*I)) L
  have hi : (∫ t : ℝ,
      Complex.exp (-((L:ℂ)*((δ:ℂ)+t*I))*(y:ℂ)) *
        profileLaplaceTransform f ((L:ℂ)*((δ:ℂ)+t*I))) =
      (L⁻¹:ℝ) • ∫ v : ℝ,
        Complex.exp (-(((L*δ:ℝ):ℂ)+v*I)*(y:ℂ)) *
          profileLaplaceTransform f (((L*δ:ℝ):ℂ)+v*I) := by
    simpa only [hw, abs_of_pos (inv_pos.mpr hL)] using hscale
  rw [hi, real_smul, Complex.ofReal_inv]
  have hLc : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  rw [← mul_assoc, div_mul_eq_mul_div, mul_inv_cancel₀ hLc, one_div]
  simpa only [one_div] using profileLaplaceTransform_inversion hf hs (L*δ) y

/-- Mellin inversion of the actual logarithmic profile `f(log n/L)`, for
positive real `n`. The complex power, scaling, and contour factors all agree
with the displayed identity in §3.1. -/
theorem profile_log_mellin_inversion {f : ℝ → ℂ}
    (hf : HasCompactSupport f) (hs : ContDiff ℝ ∞ f)
    {L n : ℝ} (hL : 0 < L) (hn : 0 < n) (δ : ℝ) :
    f (Real.log n/L) = ((L:ℂ)/(2*π)) * ∫ t : ℝ,
      profileLaplaceTransform f ((L:ℂ)*((δ:ℂ)+t*I)) *
        (n:ℂ)^(-((δ:ℂ)+t*I)) := by
  rw [profileLaplaceTransform_scaled_inversion hf hs hL δ (Real.log n/L)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hn.ne'),
    ← Complex.ofReal_log hn.le]
  have he : -((L:ℂ)*((δ:ℂ)+t*I))*((Real.log n/L:ℝ):ℂ) =
      (Real.log n:ℂ)*(-((δ:ℂ)+t*I)) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hL.ne']
  rw [he, mul_comm]

end

end Sechstmoment
