import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory Metric
open scoped ContDiff
noncomputable section

def noDPFrequencyBump : ContDiffBump (0:ℝ) :=
  ⟨1,2,by norm_num,by norm_num⟩

def noDPFourierCutoff (h : SchwartzMap ℝ ℂ) (H ξ : ℝ) : ℂ :=
  h ξ*(noDPFrequencyBump (ξ/H):ℂ)

theorem noDPFourierCutoff_contDiff (h : SchwartzMap ℝ ℂ) (H : ℝ) :
    ContDiff ℝ ∞ (noDPFourierCutoff h H) :=
  h.smooth'.mul (Complex.ofRealCLM.contDiff.comp
    (noDPFrequencyBump.contDiff.comp (by fun_prop)))

theorem noDPFourierCutoff_eq_self (h : SchwartzMap ℝ ℂ) {H ξ : ℝ}
    (hH : 0 < H) (hξ : |ξ| ≤ H) : noDPFourierCutoff h H ξ = h ξ := by
  have hb : ξ/H ∈ closedBall (0:ℝ) noDPFrequencyBump.rIn := by
    simp only [mem_closedBall,Real.dist_eq,sub_zero,noDPFrequencyBump]
    rw [abs_div,abs_of_pos hH]
    exact (div_le_one hH).mpr hξ
  simp [noDPFourierCutoff,noDPFrequencyBump.one_of_mem_closedBall hb]

theorem noDPFourierCutoff_zero (h : SchwartzMap ℝ ℂ) {H ξ : ℝ}
    (hH : 0 < H) (hξ : 2*H ≤ |ξ|) : noDPFourierCutoff h H ξ = 0 := by
  have hb : noDPFrequencyBump.rOut ≤ dist (ξ/H) (0:ℝ) := by
    simp only [Real.dist_eq,sub_zero,noDPFrequencyBump]
    rw [abs_div,abs_of_pos hH]
    exact (le_div_iff₀ hH).mpr hξ
  simp [noDPFourierCutoff,noDPFrequencyBump.zero_of_le_dist hb]

theorem noDPFourierCutoff_tsupport (h : SchwartzMap ℝ ℂ) {H : ℝ} (hH : 0 < H) :
    tsupport (noDPFourierCutoff h H) ⊆ Icc (-2*H) (2*H) := by
  apply closure_minimal _ isClosed_Icc
  intro ξ hξ
  have hnorm : |ξ| ≤ 2*H := by
    by_contra hn
    exact hξ (noDPFourierCutoff_zero h hH (le_of_lt (lt_of_not_ge hn)))
  have Habs := abs_le.mp hnorm
  exact ⟨by linarith [Habs.1],Habs.2⟩

def noDPFourierCutoffSchwartz (h : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0 < H) :
    SchwartzMap ℝ ℂ :=
  (show HasCompactSupport (noDPFourierCutoff h H) from
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (noDPFourierCutoff_tsupport h hH)).toSchwartzMap
    (noDPFourierCutoff_contDiff h H)

@[simp] theorem noDPFourierCutoffSchwartz_coe (h : SchwartzMap ℝ ℂ) (H : ℝ) (hH : 0 < H) :
    ((noDPFourierCutoffSchwartz h H hH : SchwartzMap ℝ ℂ) : ℝ → ℂ) =
      noDPFourierCutoff h H := rfl

theorem noDPFourierCutoff_norm (h : SchwartzMap ℝ ℂ) (H ξ : ℝ) :
    ‖noDPFourierCutoff h H ξ‖ ≤ ‖h ξ‖ := by
  have hb0 : 0 ≤ noDPFrequencyBump (ξ/H) := noDPFrequencyBump.nonneg
  have hb1 : noDPFrequencyBump (ξ/H) ≤ 1 := noDPFrequencyBump.le_one
  rw [noDPFourierCutoff,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hb0]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb1 (norm_nonneg (h ξ))

theorem noDPFourierCutoff_sub_norm (h : SchwartzMap ℝ ℂ) (H ξ : ℝ) :
    ‖noDPFourierCutoff h H ξ-h ξ‖ ≤ ‖h ξ‖ := by
  have hb0 : 0 ≤ noDPFrequencyBump (ξ/H) := noDPFrequencyBump.nonneg
  have hb1 : noDPFrequencyBump (ξ/H) ≤ 1 := noDPFrequencyBump.le_one
  have hb : ‖(noDPFrequencyBump (ξ/H):ℂ)-1‖ ≤ 1 := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  rw [noDPFourierCutoff,show h ξ*(noDPFrequencyBump (ξ/H):ℂ)-h ξ =
    h ξ*((noDPFrequencyBump (ξ/H):ℂ)-1) by ring,norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (norm_nonneg (h ξ))

theorem noDPFourierCutoff_weighted_tail_pointwise (h : SchwartzMap ℝ ℂ)
    {H : ℝ} (hH : 0 < H) (k M : ℕ) (ξ : ℝ) :
    H^M*(|ξ|^k*‖noDPFourierCutoff h H ξ-h ξ‖) ≤ |ξ|^(k+M)*‖h ξ‖ := by
  by_cases hξ : |ξ| ≤ H
  · rw [noDPFourierCutoff_eq_self h hH hξ,sub_self,norm_zero,mul_zero,mul_zero]
    positivity
  · have hξ' : H ≤ |ξ| := le_of_lt (lt_of_not_ge hξ)
    calc
      _ ≤ |ξ|^M*(|ξ|^k*‖h ξ‖) := by
        gcongr
        exact noDPFourierCutoff_sub_norm h H ξ
      _ = _ := by rw [pow_add]; ring

theorem noDPFourierCutoff_weighted_tail_integral (h : SchwartzMap ℝ ℂ)
    {H : ℝ} (hH : 0 < H) (k M : ℕ) :
    H^M*(∫ ξ : ℝ, |ξ|^k*‖noDPFourierCutoff h H ξ-h ξ‖) ≤
      ∫ ξ : ℝ, |ξ|^(k+M)*‖h ξ‖ := by
  let d := noDPFourierCutoffSchwartz h H hH-h
  have hd : Integrable (fun ξ : ℝ => |ξ|^k*‖noDPFourierCutoff h H ξ-h ξ‖) := by
    simpa only [d,sub_apply,noDPFourierCutoffSchwartz_coe,Real.norm_eq_abs] using
      d.integrable_pow_mul volume k
  have hi : Integrable (fun ξ : ℝ => |ξ|^(k+M)*‖h ξ‖) := by
    simpa only [Real.norm_eq_abs] using h.integrable_pow_mul volume (k+M)
  rw [← integral_const_mul]
  exact integral_mono (hd.const_mul _) hi (noDPFourierCutoff_weighted_tail_pointwise h hH k M)

end
end Sechstmoment.Source
