import Sechstmoment.Numerator.V.Asymptotic.RegularMomentLeading

/-! Transfer the proved, uniform separated estimate for the actual moment
to the whole fixed polydisc, including all coincident zeta shifts. -/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem noDPCauchyPolydisc_norm (σ : Fin 4 → ℂ)
    (hσ : σ ∈ rectangularClosedPolydisc dpCauchyRadii) : ‖σ‖ ≤ 8 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 8)).mpr
  intro j
  have hr : dpCauchyRadii j ≤ (8:ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
  exact (hσ j).trans hr

theorem noDPCauchyBoundary_gap (σ : Fin 4 → ℂ)
    (hσ : σ ∈ rectangularDistinguishedBoundary dpCauchyRadii)
    (i j : Fin 4) (hij : i ≠ j) : (1:ℝ) ≤ ‖σ i-σ j‖ := by
  have hg : (1:ℝ) ≤ |dpCauchyRadii i-dpCauchyRadii j| := by
    fin_cases i <;> fin_cases j <;> norm_num [dpCauchyRadii] at *
  have ht := abs_norm_sub_norm_le (σ i) (σ j)
  rw [hσ i,hσ j] at ht
  exact hg.trans ht

theorem critical_polynomial_collision_normalized_error {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {η ε : ℝ} (hη : 0 < η) (hηu : η < 1/4)
    (hε : 0 < ε) (hεu : ε < 1/2) (P Q : Polynomial ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ σ ∈ rectangularClosedPolydisc dpCauchyRadii, ∀ z : ℂ, ‖z‖ ≤ 8 →
      ‖noDPCriticalPolynomialMoment w T η P Q σ z/((T:ℂ)*(Real.log T:ℂ)^9)-
        noDPRegularMomentLeading w η P Q σ z‖ ≤
        C*(T^(1/2+2*η-1:ℝ)+T^(1/2+2*η+ε-1:ℝ)+1/Real.log T) := by
  obtain ⟨C,hC,U,hU,HB⟩ := critical_polynomial_separated_normalized_error
    hw hws hη hηu (by norm_num : (0:ℝ) ≤ 8) (by norm_num : (0:ℝ) < 1) hε hεu P Q
  let V := max U (Real.exp 17)
  refine ⟨C,hC,V,hU.trans_le (le_max_left _ _),?_⟩
  intro T hTV σ hσ z hz
  have hTU : U ≤ T := (le_max_left _ _).trans hTV
  have hT1 : 1 < T := hU.trans_le hTU
  have hlog : 17 ≤ Real.log T := by
    have he : Real.exp 17 ≤ T := (le_max_right _ _).trans hTV
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 17) he
  have hL0 : 0 < Real.log T := by linarith
  have hzsmall : |(z/(Real.log T:ℂ)).re| < 1/2 := by
    apply (Complex.abs_re_le_norm _).trans_lt
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
    apply (div_lt_iff₀ hL0).mpr
    linarith
  have hR : ∀ j, 2*dpCauchyRadii j < Real.log T := by
    intro j
    have hr : dpCauchyRadii j ≤ (8:ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
    linarith
  have hd := noDPCriticalPolynomialMoment_differentiableOn_polydisc
    hT1 hzsmall dpCauchyRadii hR η P Q w hw.continuous hws
  have hq : DifferentiableOn ℂ (fun τ : Fin 4 → ℂ =>
      noDPCriticalPolynomialMoment w T η P Q τ z/((T:ℂ)*(Real.log T:ℂ)^9))
      (rectangularClosedPolydisc dpCauchyRadii) :=
    by simpa only [div_eq_mul_inv] using hd.mul_const (((T:ℂ)*(Real.log T:ℂ)^9)⁻¹)
  have hf : DifferentiableOn ℂ (fun τ : Fin 4 → ℂ =>
      noDPCriticalPolynomialMoment w T η P Q τ z/((T:ℂ)*(Real.log T:ℂ)^9)-
        noDPRegularMomentLeading w η P Q τ z)
      (rectangularClosedPolydisc dpCauchyRadii) :=
    hq.sub (noDPRegularMomentLeading_differentiableOn hη.le w P Q z)
  apply rectangular_polydisc_norm_le dpCauchyRadii dpCauchyRadii_positive _ hf ?_ σ hσ
  intro τ hτ
  have hτpol : τ ∈ rectangularClosedPolydisc dpCauchyRadii := fun j => (hτ j).le
  have hinj : Function.Injective τ := by
    intro i j hij
    by_contra hn
    have hg := noDPCauchyBoundary_gap τ hτ i j hn
    rw [hij,sub_self,norm_zero] at hg
    norm_num at hg
  have hr : ∀ j, ‖τ j‖ < 16 := by
    intro j
    have hn := (norm_le_pi_norm τ j).trans (noDPCauchyPolydisc_norm τ hτpol)
    linarith
  have hb := HB T hTU τ (noDPCauchyPolydisc_norm τ hτpol) z hz
    (noDPCauchyBoundary_gap τ hτ)
  rwa [separatedResidueLeading_eq_regular hη w P Q τ z hinj hr] at hb

theorem critical_polynomial_collision_uniform_tendsto {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {η : ℝ} (hη : 0 < η) (hηu : η < 1/4) (P Q : Polynomial ℝ) :
    ∀ r : ℝ, 0 < r → ∀ᶠ T : ℝ in atTop,
      ∀ σ ∈ rectangularClosedPolydisc dpCauchyRadii, ∀ z : ℂ, ‖z‖ ≤ 8 →
      ‖noDPCriticalPolynomialMoment w T η P Q σ z/((T:ℂ)*(Real.log T:ℂ)^9)-
        noDPRegularMomentLeading w η P Q σ z‖ < r := by
  let ε : ℝ := (1/2-2*η)/2
  have hε : 0 < ε := by dsimp only [ε]; linarith
  have hεu : ε < 1/2 := by dsimp only [ε]; linarith
  obtain ⟨C,_,U,_,HB⟩ := critical_polynomial_collision_normalized_error hw hws hη hηu hε hεu P Q
  have ha : 1/2+2*η-1 < 0 := by linarith
  have hb : 1/2+2*η+ε-1 < 0 := by dsimp only [ε]; linarith
  have hta : Tendsto (fun T : ℝ => T^(1/2+2*η-1:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr ha)
  have htb : Tendsto (fun T : ℝ => T^(1/2+2*η+ε-1:ℝ)) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hb)
  have htl : Tendsto (fun T : ℝ => 1/Real.log T) atTop (𝓝 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
  have ht := ((hta.add htb).add htl).const_mul C
  simp only [add_zero,mul_zero] at ht
  intro r hr
  filter_upwards [eventually_ge_atTop U,(tendsto_order.1 ht).2 r hr] with T hT hlim
  intro σ hσ z hz
  exact (HB T hT σ hσ z hz).trans_lt hlim

theorem critical_polynomial_collision_normalized_tendsto {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {η : ℝ} (hη : 0 < η) (hηu : η < 1/4) (P Q : Polynomial ℝ)
    (σ : Fin 4 → ℂ) (hσ : σ ∈ rectangularClosedPolydisc dpCauchyRadii)
    (z : ℂ) (hz : ‖z‖ ≤ 8) :
    Tendsto (fun T : ℝ => noDPCriticalPolynomialMoment w T η P Q σ z/
      ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 (noDPRegularMomentLeading w η P Q σ z)) := by
  apply Metric.tendsto_nhds.2
  intro r hr
  filter_upwards [critical_polynomial_collision_uniform_tendsto hw hws hη hηu P Q r hr]
    with T hT
  simpa only [dist_eq_norm] using hT σ hσ z hz

end
end Sechstmoment.Source
