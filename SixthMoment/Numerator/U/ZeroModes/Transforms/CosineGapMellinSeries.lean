import SixthMoment.Numerator.U.ZeroModes.Transforms.CosineGapMellinSeriesBase

namespace SixthMoment
open Complex Real Set Filter MeasureTheory Source
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem a03SmoothedCosine_inverse_kernel_integrable {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c R : ℝ} (hc : 0<c) (hR : 0<R) :
    Integrable (fun v : ℝ => (R:ℂ)^(-((c:ℂ)+(v:ℂ)*I))*
      mellin (a03SmoothedCosine Φ) ((c:ℂ)+(v:ℂ)*I)) := by
  have hm := a03SmoothedCosine_vertical_integrable hΦ hSupp hc
  have hp : Continuous (fun v : ℝ => (R:ℂ)^(-((c:ℂ)+(v:ℂ)*I))) := by
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hR.ne')]
    fun_prop
  apply (hm.norm.const_mul (R^(-c))).mono' (hp.aestronglyMeasurable.mul hm.1)
  apply ae_of_all
  intro v
  dsimp only [Pi.mul_apply]
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hR]
  simp

theorem a03SmoothedCosine_gap_inverse_integral {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c R : ℝ} (hc : 0<c) (hR : 0<R) (h : ℕ) :
    a03SmoothedCosine Φ (R*((h:ℝ)+1))=
      (1/(2*Real.pi):ℂ)*(∫ v : ℝ,(((h:ℝ)+1:ℝ):ℂ)^(-((c:ℂ)+(v:ℂ)*I))*
        ((R:ℂ)^(-((c:ℂ)+(v:ℂ)*I))*mellin (a03SmoothedCosine Φ) ((c:ℂ)+(v:ℂ)*I))) := by
  rw [←a03SmoothedCosine_mellinInv_mellin hΦ hSupp hc (mul_pos hR (by positivity))]
  unfold mellinInv
  simp only [Complex.real_smul,smul_eq_mul]
  push_cast
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro v
  dsimp only
  have he := Complex.mul_cpow_ofReal_nonneg hR.le
    (show (0:ℝ)≤(h:ℝ)+1 by positivity) (-((c:ℂ)+(v:ℂ)*I))
  push_cast at he
  rw [he]
  ring

theorem a03SmoothedCosine_gap_norm_summable {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c R : ℝ} (hc : 1<c) (hR : 0<R) :
    Summable (fun h : ℕ => ‖a03SmoothedCosine Φ (R*((h:ℝ)+1))‖) := by
  let K : ℝ→ℂ := fun v => (R:ℂ)^(-((c:ℂ)+(v:ℂ)*I))*
    mellin (a03SmoothedCosine Φ) ((c:ℂ)+(v:ℂ)*I)
  have hK := a03SmoothedCosine_inverse_kernel_integrable hΦ hSupp (zero_lt_one.trans hc) hR
  have hs : Summable (fun h : ℕ => ‖(1/(2*Real.pi):ℂ)‖*
      (((h:ℝ)+1)^(-c)*(∫ v : ℝ,‖K v‖))) :=
    ((a03GapPower_summable hc).mul_right (∫ v : ℝ,‖K v‖)).mul_left _
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro h
  rw [a03SmoothedCosine_gap_inverse_integral hΦ hSupp (zero_lt_one.trans hc) hR,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_integral_le_integral_norm _).trans_eq (a03GapPower_integral_norm hK h)

theorem a03SmoothedCosine_gap_sum_inverse_Mellin {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c R : ℝ} (hc : 1<c) (hR : 0<R) :
    (∑' h : ℕ,a03SmoothedCosine Φ (R*((h:ℝ)+1)))=
      verticalIntegral c (fun s : ℂ => (R:ℂ)^(-s)*riemannZeta s*
        (Complex.Gamma s*Complex.cos ((Real.pi:ℂ)*s/2)*mellin Φ (1-s))) := by
  have hK := a03SmoothedCosine_inverse_kernel_integrable hΦ hSupp (zero_lt_one.trans hc) hR
  simp_rw [a03SmoothedCosine_gap_inverse_integral hΦ hSupp (zero_lt_one.trans hc) hR]
  rw [tsum_mul_left,a03GapPower_integral_tsum hc hK]
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro v
  dsimp only
  rw [a03SmoothedCosine_mellin_eq_gamma_mellin hΦ hSupp (by simpa using (zero_lt_one.trans hc))]
  ring

end
end SixthMoment
