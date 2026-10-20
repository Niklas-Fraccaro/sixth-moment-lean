import SixthMoment.Numerator.V.Chi.CosineInversion


namespace SixthMoment.Source
open Complex Real Set MeasureTheory
open scoped ContDiff
noncomputable section

theorem positive_dilate_tsupport {g : ℝ → ℂ} {a : ℝ} (ha : 0 < a)
    (hg : tsupport g ⊆ Icc a (2*a)) :
    tsupport (fun u : ℝ => g (a*u)) ⊆ Icc (1:ℝ) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  have H := hg (subset_tsupport g hu)
  constructor
  · exact (mul_le_mul_iff_of_pos_left ha).mp (by simpa only [mul_one] using H.1)
  · exact (mul_le_mul_iff_of_pos_left ha).mp (H.2.trans_eq (mul_comm 2 a))

theorem chi_cosine_inverse_mellin_dilate {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) {a : ℝ} (ha : 0 < a)
    (hSupp : tsupport g ⊆ Icc a (2*a))
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    verticalIntegral c (fun s : ℂ =>
      (r:ℂ)^(-s)*zetaChi (1-s)*mellin g (1-s)) =
      2*(a:ℂ)*a03SmoothedCosine (fun u => g (a*u)) (2*Real.pi*(a*r)) := by
  let Φ : ℝ → ℂ := fun u => g (a*u)
  have hΦ : ContDiff ℝ ∞ Φ := hg.comp (by fun_prop)
  have hΦs : tsupport Φ ⊆ Icc (1:ℝ) 2 := positive_dilate_tsupport ha hSupp
  have he (s : ℂ) :
      (a:ℂ)*((a*r:ℝ):ℂ)^(-s)*mellin Φ (1-s) =
        (r:ℂ)^(-s)*mellin g (1-s) := by
    have hpow : (a:ℂ)^(-s)*(a:ℂ)^(-(1-s)) = (a:ℂ)^(-1:ℂ) := by
      rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne')]
      congr 1
      ring
    dsimp only [Φ]
    rw [mellin_comp_mul_left g (1-s) ha,smul_eq_mul,Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg ha.le hr.le]
    calc
      _ = ((a:ℂ)*((a:ℂ)^(-s)*(a:ℂ)^(-(1-s))))*
          (r:ℂ)^(-s)*mellin g (1-s) := by ring
      _ = _ := by
        rw [hpow,Complex.cpow_neg_one,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne'),one_mul]
  calc
    _ = (a:ℂ)*verticalIntegral c (fun s : ℂ =>
        ((a*r:ℝ):ℂ)^(-s)*zetaChi (1-s)*mellin Φ (1-s)) := by
      have hpoint (t : ℝ) :
          (r:ℂ)^(-((c:ℂ)+(t:ℂ)*I))*zetaChi (1-((c:ℂ)+(t:ℂ)*I))*
              mellin g (1-((c:ℂ)+(t:ℂ)*I)) =
          (a:ℂ)*(((a*r:ℝ):ℂ)^(-((c:ℂ)+(t:ℂ)*I))*
            zetaChi (1-((c:ℂ)+(t:ℂ)*I))*mellin Φ (1-((c:ℂ)+(t:ℂ)*I))) := by
        have H := congrArg (fun z : ℂ => z*zetaChi (1-((c:ℂ)+(t:ℂ)*I)))
          (he ((c:ℂ)+(t:ℂ)*I))
        linear_combination -H
      unfold verticalIntegral
      simp_rw [hpoint]
      rw [integral_const_mul]
      ring
    _ = _ := by
      rw [chi_cosine_inverse_mellin hΦ hΦs hc (mul_pos ha hr)]
      ring

theorem smoothed_cosine_positive_dilate {g : ℝ → ℂ}
    (hg : Continuous g) {a : ℝ} (ha : 0 < a)
    (hSupp : tsupport g ⊆ Icc a (2*a)) (x : ℝ) :
    (a:ℂ)*a03SmoothedCosine (fun u => g (a*u)) (a*x) =
      a03SmoothedCosine g x := by
  have hK : HasCompactSupport g :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hSupp
  have hKd : HasCompactSupport (fun u : ℝ => g (a*u)) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (positive_dilate_tsupport ha hSupp)
  rw [a03SmoothedCosine_eq_time_integral (Φ := fun u : ℝ => g (a*u))
      (hg.comp (by fun_prop)) hKd,
    a03SmoothedCosine_eq_time_integral (Φ := g) hg hK]
  let F : ℝ → ℂ := fun u => (Real.cos (u*x):ℂ)*g u
  have he : (fun u : ℝ => (Real.cos (u*(a*x)):ℂ)*g (a*u)) =
      fun u : ℝ => F (a*u) := by
    funext u
    dsimp only [F]
    congr 2
    ring
  rw [he,Measure.integral_comp_mul_left F a]
  simp [F,abs_of_pos (inv_pos.mpr ha),RCLike.real_smul_eq_coe_mul,ha.ne']

theorem chi_cosine_inverse_mellin_positive_profile {g : ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) {a : ℝ} (ha : 0 < a)
    (hSupp : tsupport g ⊆ Icc a (2*a))
    {c r : ℝ} (hc : 0 < c) (hr : 0 < r) :
    verticalIntegral c (fun s : ℂ =>
      (r:ℂ)^(-s)*zetaChi (1-s)*mellin g (1-s)) =
      2*a03SmoothedCosine g (2*Real.pi*r) := by
  rw [chi_cosine_inverse_mellin_dilate hg ha hSupp hc hr,
    show 2*Real.pi*(a*r) = a*(2*Real.pi*r) by ring,mul_assoc,
    smoothed_cosine_positive_dilate hg.continuous ha hSupp]

end
end SixthMoment.Source
