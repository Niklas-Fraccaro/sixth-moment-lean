import SixthMoment.Numerator.U.ZeroModes.Transforms.GammaCosStripGrowth
import SixthMoment.Numerator.V.Chi.CosineInversion


namespace SixthMoment.Source
open Complex Real Set MeasureTheory
noncomputable section

theorem chi_vertical_aestronglyMeasurable {c : ℝ} (hc : 0 < c) :
    AEStronglyMeasurable (fun t : ℝ => zetaChi (1-((c:ℂ)+(t:ℂ)*I))) volume := by
  let a : ℂ := ((2*Real.pi:ℝ):ℂ)
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hpow : Continuous (fun t : ℝ => a^(-((c:ℂ)+(t:ℂ)*I))) := by
    have he : (fun t : ℝ => a^(-((c:ℂ)+(t:ℂ)*I))) =
        fun t : ℝ => Complex.exp (Complex.log a*(-((c:ℂ)+(t:ℂ)*I))) := by
      funext t
      exact Complex.cpow_def_of_ne_zero ha _
    rw [he]
    fun_prop
  have hcont : Continuous (fun t : ℝ =>
      2*a^(-((c:ℂ)+(t:ℂ)*I))*
        (Complex.Gamma ((c:ℂ)+(t:ℂ)*I)*
          Complex.cos ((Real.pi:ℂ)*((c:ℂ)+(t:ℂ)*I)/2))) :=
    (continuous_const.mul hpow).mul (a03GammaCos_vertical_continuous hc)
  apply hcont.aestronglyMeasurable.congr
  filter_upwards [volume.ae_ne (0:ℝ)] with t ht
  rw [chi_one_sub_eq_gamma_cos _ (by simpa using ht)]
  dsimp only [a]
  ring

theorem chi_positive_strip_global_polynomial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ c ∈ Icc (1/8:ℝ) (15/8), ∀ t : ℝ, t ≠ 0 →
      ‖zetaChi (1-((c:ℂ)+(t:ℂ)*I))‖ ≤ C*(1+|t|)^2 := by
  obtain ⟨D,hD,hgamma⟩ := a03GammaCos_strip_polynomial_bound
  refine ⟨2*D+1,by positivity,?_⟩
  intro c hc t ht
  have hp : 0 < 2*Real.pi := by positivity
  have hp1 : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have hpow : ‖((2*Real.pi:ℝ):ℂ)^(-((c:ℂ)+(t:ℂ)*I))‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp only [neg_re,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]
    exact Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith [hc.1])
  have hg := hgamma ((c:ℂ)+(t:ℂ)*I) (by
    simp only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]
    constructor <;> linarith [hc.1,hc.2])
  simp only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add] at hg
  rw [chi_one_sub_eq_gamma_cos _ (by simpa using ht)]
  rw [show 2*((2*Real.pi:ℝ):ℂ)^(-((c:ℂ)+(t:ℂ)*I))*
      Complex.Gamma ((c:ℂ)+(t:ℂ)*I)*Complex.cos ((Real.pi:ℂ)*((c:ℂ)+(t:ℂ)*I)/2) =
      2*(((2*Real.pi:ℝ):ℂ)^(-((c:ℂ)+(t:ℂ)*I)))*
        (Complex.Gamma ((c:ℂ)+(t:ℂ)*I)*Complex.cos ((Real.pi:ℂ)*((c:ℂ)+(t:ℂ)*I)/2)) by ring]
  rw [norm_mul,norm_mul,show ‖(2:ℂ)‖ = 2 by norm_num]
  calc
    _ ≤ (2*1)*(D*(1+|t|)^2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num)) hg (norm_nonneg _) (by norm_num)
    _ ≤ _ := by nlinarith [sq_nonneg (1+|t|)]

end
end SixthMoment.Source
