import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import SixthMoment.Numerator.U.Diagonal.ProfileHolomorphy
import SixthMoment.Numerator.U.ZeroModes.Transforms.PositiveTimeMellinDecay
import SixthMoment.Numerator.U.ZeroModes.Transforms.SmoothedCosineGamma

namespace SixthMoment
open Complex Real Set Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem a03PositiveTime_inversePowerIntegral_eq_mellin {Φ : ℝ→ℂ}
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (s : ℂ) :
    (∫ t : ℝ,Φ t*(t:ℂ)^(-s))=mellin Φ (1-s) := by
  unfold mellin
  rw [show 1-s-1=-s by ring,←integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  by_cases ht : t∈Ioi (0:ℝ)
  · rw [indicator_of_mem ht,smul_eq_mul]
    ring
  · have hz : Φ t=0 := by
      by_contra hn
      have hs := hSupp (subset_tsupport Φ hn)
      exact ht (zero_lt_one.trans_le hs.1)
    simp [hz,indicator_of_notMem ht]

theorem a03SmoothedCosine_mellin_eq_gamma_mellin {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {s : ℂ} (hs : 0<s.re) :
    mellin (a03SmoothedCosine Φ) s=
      Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*mellin Φ (1-s) := by
  rw [a03SmoothedCosine_mellin_eq_gamma hΦ hSupp hs,
    a03PositiveTime_inversePowerIntegral_eq_mellin hSupp]

theorem a03PositiveTimeMellin_line_continuous {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (a : ℝ) :
    Continuous (fun v : ℝ => mellin Φ ((a:ℂ)+(v:ℂ)*I)) := by
  have he : (fun v : ℝ => mellin Φ ((a:ℂ)+(v:ℂ)*I))=
      fun v : ℝ => profileLaplaceTransform (a03PositiveTimeLogProfile Φ a) (((-v:ℝ):ℂ)*I) := by
    funext v
    exact a03PositiveTimeMellin_eq_laplace Φ a v
  rw [he]
  exact (profileLaplaceTransform_differentiable (a03PositiveTimeLogProfile_compact hSupp a)
    (a03PositiveTimeLogProfile_contDiff hΦ a).continuous).continuous.comp (by fun_prop)

theorem a03GammaCos_vertical_continuous {c : ℝ} (hc : 0<c) :
    Continuous (fun v : ℝ => Complex.Gamma ((c:ℂ)+(v:ℂ)*I)*
      Complex.cos ((Real.pi:ℂ)*((c:ℂ)+(v:ℂ)*I)/2)) := by
  have hg : Continuous (fun v : ℝ => Complex.Gamma ((c:ℂ)+(v:ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    have hp (m : ℕ) : (c:ℂ)+(v:ℂ)*I≠-(m:ℂ) := by
      intro he
      have hr := congrArg Complex.re he
      simp only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero,neg_re,natCast_re] at hr
      have hm : (0:ℝ)≤m := Nat.cast_nonneg m
      linarith
    exact ContinuousAt.comp' (f:=fun u : ℝ => (c:ℂ)+(u:ℂ)*I) (g:=Complex.Gamma)
      (Complex.differentiableAt_Gamma _ hp).continuousAt
      (by fun_prop : ContinuousAt (fun u : ℝ => (c:ℂ)+(u:ℂ)*I) v)
  exact hg.mul (by fun_prop)

theorem a03SmoothedCosine_vertical_integrable_of_GammaCos_bound {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c C : ℝ} (hc : 0<c) (hC : 0≤C) (N : ℕ)
    (hΓ : ∀ v : ℝ,‖Complex.Gamma ((c:ℂ)+(v:ℂ)*I)*
      Complex.cos ((Real.pi:ℂ)*((c:ℂ)+(v:ℂ)*I)/2)‖≤C*(1+|v|)^N) :
    VerticalIntegrable (mellin (a03SmoothedCosine Φ)) c := by
  obtain ⟨D,hD,hPhi⟩ := a03PositiveTimeMellin_full_height_decay hΦ hSupp (1-c) (N+2)
  have hcont : Continuous (fun v : ℝ => mellin (a03SmoothedCosine Φ) ((c:ℂ)+(v:ℂ)*I)) := by
    have hM : Continuous (fun v : ℝ => mellin Φ (1-((c:ℂ)+(v:ℂ)*I))) := by
      have he : (fun v : ℝ => mellin Φ (1-((c:ℂ)+(v:ℂ)*I)))=
          fun v : ℝ => mellin Φ (((1-c:ℝ):ℂ)+((-v:ℝ):ℂ)*I) := by
        funext v
        congr 1
        push_cast
        ring
      rw [he]
      exact (a03PositiveTimeMellin_line_continuous hΦ hSupp (1-c)).comp continuous_neg
    have he : (fun v : ℝ => mellin (a03SmoothedCosine Φ) ((c:ℂ)+(v:ℂ)*I))=
        fun v : ℝ => (Complex.Gamma ((c:ℂ)+(v:ℂ)*I)*Complex.cos ((Real.pi:ℂ)*((c:ℂ)+(v:ℂ)*I)/2))*
          mellin Φ (1-((c:ℂ)+(v:ℂ)*I)) := by
      funext v
      exact a03SmoothedCosine_mellin_eq_gamma_mellin hΦ hSupp (by simpa using hc)
    rw [he]
    exact (a03GammaCos_vertical_continuous hc).mul hM
  apply (integrable_inv_one_add_sq.const_mul (C*D)).mono' hcont.aestronglyMeasurable
  apply ae_of_all
  intro v
  let x : ℝ := 1+|v|
  have hx : 0<x := by dsimp [x]; positivity
  have hPh : ‖mellin Φ (1-((c:ℂ)+(v:ℂ)*I))‖≤D/x^(N+2) := by
    have hp := hPhi (-v)
    simp only [abs_neg] at hp
    have he : 1-((c:ℂ)+(v:ℂ)*I)=((1-c:ℝ):ℂ)+((-v:ℝ):ℂ)*I := by push_cast; ring
    rw [←he] at hp
    exact (le_div_iff₀ (pow_pos hx _)).mpr (by simpa only [mul_comm] using hp)
  rw [a03SmoothedCosine_mellin_eq_gamma_mellin hΦ hSupp (by simpa using hc),norm_mul]
  calc
    _≤(C*x^N)*(D/x^(N+2)) := mul_le_mul (hΓ v) hPh (norm_nonneg _) (by positivity)
    _=C*D/x^2 := by rw [pow_add]; field_simp
    _≤(C*D)*(1+v^2)⁻¹ := by
      have hp : 1+v^2≤x^2 := by dsimp [x]; nlinarith [sq_abs v,abs_nonneg v]
      have hden : 0<1+v^2 := by positivity
      have hd := div_le_div_of_nonneg_left (mul_nonneg hC hD) hden hp
      simpa only [div_eq_mul_inv] using hd

end
end SixthMoment
