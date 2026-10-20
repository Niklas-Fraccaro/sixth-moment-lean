import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import SixthMoment.Numerator.U.Separation.DualLeadingRegularity
import SixthMoment.Numerator.U.ZeroModes.LeadingFubini
import SixthMoment.Numerator.U.ZeroModes.Linearization.Kernels

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory Metric
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_log_one_add_sub_self_abs_le {x : ℝ} (hx : |x|≤1/2) :
    |Real.log (1+x)-x|≤2*x^2 := by
  have hlo := (abs_le.mp hx).1
  have hp : 0<1+x := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hu := Real.log_le_sub_one_of_pos hp
  have he : x-1+(1+x)⁻¹=x^2/(1+x) := by field_simp; ring
  rw [abs_of_nonpos (by linarith : Real.log (1+x)-x≤0)]
  calc
    _≤x-1+(1+x)⁻¹ := by linarith
    _=x^2/(1+x) := he
    _≤2*x^2 := (div_le_iff₀ hp).mpr (by nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0≤1+2*x)])

private theorem exp_I_sub_bound (x y : ℝ) :
    ‖Complex.exp (I*(x:ℂ))-Complex.exp (I*(y:ℂ))‖≤|x-y| := by
  have he : Complex.exp (I*(x:ℂ))-Complex.exp (I*(y:ℂ))=
      Complex.exp (I*(y:ℂ))*(Complex.exp (I*((x-y:ℝ):ℂ))-1) := by
    rw [mul_sub,←Complex.exp_add,mul_one]
    congr 2
    push_cast
    ring
  rw [he,norm_mul,Complex.norm_exp_I_mul_ofReal,one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

theorem a03_profile_laplace_imaginary_lipschitz {F : ℝ→ℂ} (hF : Continuous F)
    (hs : tsupport F⊆Icc (1:ℝ) 2) {D : ℝ} (_hD : 0≤D)
    (hb : ∀ x∈Icc (1:ℝ) 2,‖F x‖≤D) (ξ ζ : ℝ) :
    ‖profileLaplaceTransform F ((ξ:ℂ)*I)-profileLaplaceTransform F ((ζ:ℂ)*I)‖≤2*D*|ξ-ζ| := by
  have hK : HasCompactSupport F := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  have hi (u : ℝ) : Integrable (fun x : ℝ => Complex.exp (((u:ℂ)*I)*(x:ℂ))*F x) :=
    (by fun_prop : Continuous (fun x : ℝ => Complex.exp (((u:ℂ)*I)*(x:ℂ))*F x)).integrable_of_hasCompactSupport hK.mul_left
  unfold profileLaplaceTransform
  rw [←integral_sub (hi ξ) (hi ζ)]
  have hz : ∀ x : ℝ,x∉Icc (1:ℝ) 2 →
      Complex.exp (((ξ:ℂ)*I)*(x:ℂ))*F x-Complex.exp (((ζ:ℂ)*I)*(x:ℂ))*F x=0 := by
    intro x hx
    have h0 : F x=0 := Function.notMem_support.mp (fun hn => hx (hs (subset_tsupport _ hn)))
    simp [h0]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hp : ∀ x∈Icc (1:ℝ) 2,
      ‖Complex.exp (((ξ:ℂ)*I)*(x:ℂ))*F x-Complex.exp (((ζ:ℂ)*I)*(x:ℂ))*F x‖≤2*D*|ξ-ζ| := by
    intro x hx
    rw [←sub_mul,norm_mul]
    have he : ‖Complex.exp (((ξ:ℂ)*I)*(x:ℂ))-Complex.exp (((ζ:ℂ)*I)*(x:ℂ))‖≤2*|ξ-ζ| := by
      have ht := exp_I_sub_bound (ξ*x) (ζ*x)
      have harg (u : ℝ) : I*((u*x:ℝ):ℂ)=((u:ℂ)*I)*(x:ℂ) := by push_cast; ring
      rw [harg ξ,harg ζ,show ξ*x-ζ*x=(ξ-ζ)*x by ring,abs_mul,abs_of_nonneg (by linarith [hx.1] : 0≤x)] at ht
      exact ht.trans ((mul_le_mul_of_nonneg_left hx.2 (abs_nonneg (ξ-ζ))).trans_eq (by ring))
    exact (mul_le_mul he (hb x hx) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hm := norm_setIntegral_le_of_norm_le_const_ae'
    (measure_Icc_lt_top : volume (Icc (1:ℝ) 2)<⊤) (ae_of_all volume hp)
  simpa only [Real.volume_real_Icc,show max (2-1:ℝ) 0=1 by norm_num,one_mul,mul_one] using hm

theorem a03_leading_frequency_uniform_lipschitz
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hs : tsupport Φ⊆Icc (1:ℝ) 2)
    {c ε κ θ R : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual : Bool,∀ ξ ζ : ℝ,
      ‖(if dual then a03GaussianDualLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I) ξ
        else a03GaussianLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I) ξ)-
        (if dual then a03GaussianDualLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I) ζ
        else a03GaussianLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I) ζ)‖≤C*T^ε*|ξ-ζ| := by
  have hK : HasCompactSupport Φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  obtain ⟨P,hP,hPd⟩ := a03_profile_derivative_bounds hK hΦ
  obtain ⟨B,hB,hBd⟩ := bblrGaussianTimeAmplitude_uniform_subpower_derivatives hc hc1 hε hκ
  obtain ⟨E,hE,hEd⟩ := bblrGaussianTimeReplacementAmplitude_uniform_subpower_derivatives hc hc1 hε hκ
  obtain ⟨D,hD,hd⟩ := bblrDualLeadingMultiplier_uniform_normalized_bound
    (closedBall (0:MomentShifts) R) (isCompact_closedBall _ _)
  let C := 2*(1+D)*(P 0*(B 0+E 0))
  have hP0 := hP 0
  have hB0 := hB 0
  have hE0 := hE 0
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hd,bblrGamma_logarithmic_strip_large hc.le hc1 hθ,eventually_ge_atTop (10:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hd hlarge hT hlog
  intro σ α hσ hα hroot v hv dual ξ ζ
  have hTp : 0<T := by linarith
  have hT1 : 1≤T := by linarith
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  let F := a03GaussianLeadingTimeProfile Φ T σ α z
  have hFc := a03GaussianLeadingTimeProfile_continuous hΦ.continuous hs hTp σ α z
  have hFs : tsupport F⊆Icc (1:ℝ) 2 := (a03_profile_product_tsupport _ _).trans hs
  have hfb (x : ℝ) (hx : x∈Icc (1:ℝ) 2) : ‖F x‖≤(P 0*(B 0+E 0))*T^ε := by
    have hp : ‖Φ x‖≤P 0 := by simpa using hPd 0 x
    have ha : ‖bblrGaussianTimeAmplitude T σ α z x‖≤B 0*T^ε := by
      simpa using hBd T (1/4:ℝ) σ α v x (by linarith) hlog (by norm_num)
        (by norm_num; exact hT) hα hroot (hlarge v hv) hx 0
    have he : ‖bblrGaussianTimeReplacementAmplitude T σ α z x‖≤E 0*T^ε := by
      have he := hEd T σ α v x hT hlog hα hroot (hlarge v hv) hx 0
      simp only [iteratedDeriv_zero] at he
      exact he.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith : ε-1≤ε)) hE0)
    have heq : F x=Φ x*(bblrGaussianTimeAmplitude T σ α z x-bblrGaussianTimeReplacementAmplitude T σ α z x) := by
      unfold F a03GaussianLeadingTimeProfile a03ProfileProduct bblrGaussianTimeAmplitude bblrGaussianTimeReplacementAmplitude
      ring
    rw [heq,norm_mul]
    exact (mul_le_mul hp ((norm_sub_le _ _).trans (add_le_add ha he)) (norm_nonneg _) hP0).trans_eq (by ring)
  have hσK : σ∈closedBall (0:MomentShifts) R := by
    rw [mem_closedBall,dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hR).mpr hσ
  have hDb (x : ℝ) (hx : x∈Icc (1:ℝ) 2) : ‖bblrDualLeadingMultiplier T σ x‖≤D := by
    have ht : T*x∈Icc T (2*T) := ⟨by nlinarith [hx.1],by nlinarith [hx.2]⟩
    simpa only [mul_div_cancel_left₀ x hTp.ne'] using hd σ hσK (T*x) ht
  cases dual
  · simp only [Bool.false_eq_true,ite_false]
    have hh := a03_profile_laplace_imaginary_lipschitz hFc hFs (by positivity) hfb ξ ζ
    exact hh.trans (by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hP0 (add_nonneg hB0 hE0)) (Real.rpow_nonneg hTp.le ε)) (abs_nonneg (ξ-ζ))])
  · simp only [ite_true]
    let Fd := a03GaussianDualLeadingTimeProfile Φ T σ α z
    have hFdc := a03GaussianDualLeadingTimeProfile_continuous hΦ.continuous hs hTp σ α z
    have hFds : tsupport Fd⊆Icc (1:ℝ) 2 := ((a03_profile_product_tsupport _ _).trans (a03_profile_product_tsupport _ _)).trans hs
    have hfdb (x : ℝ) (hx : x∈Icc (1:ℝ) 2) : ‖Fd x‖≤D*(P 0*(B 0+E 0))*T^ε := by
      have heq : Fd x=bblrDualLeadingMultiplier T σ x*F x := by
        unfold Fd F a03GaussianDualLeadingTimeProfile a03GaussianLeadingTimeProfile a03ProfileProduct
        ring
      rw [heq,norm_mul]
      exact (mul_le_mul (hDb x hx) (hfb x hx) (norm_nonneg _) hD.le).trans_eq (by ring)
    have hh := a03_profile_laplace_imaginary_lipschitz hFdc hFds (by positivity) hfdb ξ ζ
    exact hh.trans (by dsimp [C]; nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hP0 (add_nonneg hB0 hE0)) (Real.rpow_nonneg hTp.le ε)) (abs_nonneg (ξ-ζ))])

end
end SixthMoment
