import Sechstmoment.Zeta.Bounds.ZetaStripGrowth

/-! Actual polynomial bounds for the archimedean factor on the contour
used in the same-side fourth-zeta reduction. Exponential factors cancel
using reflection; no Stirling estimate is assumed.
-/

namespace Sechstmoment.Source
open Complex Real Set
open scoped Topology
noncomputable section

theorem gamma_large_unit_strip_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc (0 : ℝ) 1 → 20 ≤ |z.im| →
      ‖Complex.Gamma z‖ ≤ C*(1+|z.im|)^2*Real.exp (-(Real.pi*|z.im|/2)) := by
  obtain ⟨C,hC,hbound⟩ := gamma_compact_strip_envelopes (1/4) (3/4) (by norm_num) (by norm_num)
  refine ⟨2*C,by positivity,?_⟩
  intro z hz ht
  have h := (gamma_unit_strip_large_relative z.re z.im hz ht).1
  rw [Complex.re_add_im] at h
  have hb := (hbound ((1/2 : ℂ)+(z.im : ℂ)*I) (by simp; norm_num)).1
  simp only [add_im,div_ofNat_im,one_im,zero_div,mul_I_im,ofReal_re,zero_add] at hb
  calc
    _ ≤ 2*(1+|z.im|)*‖Complex.Gamma ((1/2 : ℂ)+(z.im : ℂ)*I)‖ := h
    _ ≤ 2*(1+|z.im|)*(C*(1+|z.im|)*Real.exp (-(Real.pi*|z.im|/2))) := by gcongr
    _ = _ := by ring

theorem gamma_large_nonnegative_strip_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc (0 : ℝ) 2 → 20 ≤ |z.im| →
      ‖Complex.Gamma z‖ ≤ C*(1+|z.im|)^3*Real.exp (-(Real.pi*|z.im|/2)) := by
  obtain ⟨C,hC,hbound⟩ := gamma_large_unit_strip_upper
  refine ⟨C,hC,?_⟩
  intro z hz ht
  by_cases hz1 : z.re ≤ 1
  · have hp : (1+|z.im|)^2 ≤ (1+|z.im|)^3 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg z.im]) (by norm_num)
    exact (hbound z ⟨hz.1,hz1⟩ ht).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC.le) (Real.exp_pos _).le)
  · have hsub : (z-1).re ∈ Icc (0 : ℝ) 1 := by
      simp only [sub_re,one_re]
      constructor <;> linarith [hz.2]
    have him : (z-1).im = z.im := by simp
    have hsub0 : z-1 ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      simp only [him,zero_im] at hi
      norm_num [hi] at ht
    have he : Complex.Gamma z = (z-1)*Complex.Gamma (z-1) := by
      simpa using Complex.Gamma_add_one (z-1) hsub0
    have hnorm : ‖z-1‖ ≤ 1+|z.im| := by
      have h := Complex.norm_le_abs_re_add_abs_im (z-1)
      rw [abs_of_nonneg hsub.1,him] at h
      linarith [hsub.2]
    rw [he,norm_mul]
    calc
      _ ≤ (1+|z.im|)*(C*(1+|z.im|)^2*Real.exp (-(Real.pi*|z.im|/2))) := by
        gcongr
        simpa only [him] using hbound (z-1) hsub (by simpa only [him] using ht)
      _ = _ := by ring

theorem zetaChi_one_sub_reflection {s : ℂ} (hs : s.im ≠ 0) :
    zetaChi (1-s) = (Real.pi : ℂ)^(1/2-s)*Complex.Gamma (s/2)*
      (Complex.Gamma ((1+s)/2)*Complex.sin ((Real.pi : ℂ)*((1-s)/2))/Real.pi) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have him : ((1-s)/2).im ≠ 0 := by
    rw [Complex.div_ofNat_im,sub_im,one_im,zero_sub]
    exact div_ne_zero (neg_ne_zero.mpr hs) (by norm_num)
  rw [zetaChi,sub_sub_cancel,Complex.Gammaℝ_def,Complex.Gammaℝ_def,
    mul_div_mul_comm,← Complex.cpow_sub _ _ hπ,
    div_eq_mul_inv (Complex.Gamma (s/2)) (Complex.Gamma ((1-s)/2)),gamma_inv_reflection_nonreal him,
    show 1-(1-s)/2 = (1+s)/2 by ring,show -s/2-(-(1-s)/2) = 1/2-s by ring]
  ring

theorem gamma_differentiableAt_nonreal {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ Complex.Gamma s := by
  apply Complex.differentiableAt_Gamma
  intro n h
  exact hs (by simpa using congrArg Complex.im h)

theorem zetaChi_one_sub_differentiableAt_nonreal {s : ℂ} (hs : s.im ≠ 0) :
    DifferentiableAt ℂ (fun z => zetaChi (1-z)) s := by
  have heq : (fun z => zetaChi (1-z)) =ᶠ[𝓝 s]
      (fun z => (Real.pi : ℂ)^(1/2-z)*Complex.Gamma (z/2)*
        (Complex.Gamma ((1+z)/2)*Complex.sin ((Real.pi : ℂ)*((1-z)/2))/Real.pi)) := by
    have hn : ∀ᶠ z : ℂ in 𝓝 s, z.im ≠ 0 :=
      Complex.continuous_im.continuousAt.eventually_ne hs
    filter_upwards [hn] with z hz
    exact zetaChi_one_sub_reflection hz
  apply DifferentiableAt.congr_of_eventuallyEq _ heq
  have hi : (s/2).im ≠ 0 := by rw [Complex.div_ofNat_im]; exact div_ne_zero hs (by norm_num)
  have hi' : ((1+s)/2).im ≠ 0 := by
    rw [Complex.div_ofNat_im,add_im,one_im,zero_add]
    exact div_ne_zero hs (by norm_num)
  have hG := (gamma_differentiableAt_nonreal hi).comp s (differentiableAt_id.div_const (2 : ℂ))
  have hG' := (gamma_differentiableAt_nonreal hi').comp s
    ((differentiableAt_const (1 : ℂ)).add differentiableAt_id |>.div_const (2 : ℂ))
  have hP : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ)^(1/2-z)) s := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact (hP.mul hG).mul ((hG'.mul (by fun_prop)).div_const _)

theorem zetaChi_one_sub_polynomial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (3/2) → 40 ≤ |s.im| →
      ‖zetaChi (1-s)‖ ≤ C*(1+|s.im|)^4 := by
  obtain ⟨A,hA,hgamma⟩ := gamma_compact_strip_envelopes (1/4) (3/4) (by norm_num) (by norm_num)
  obtain ⟨B,hB,hgamma'⟩ := gamma_large_nonnegative_strip_upper
  refine ⟨A*B,by positivity,?_⟩
  intro s hs ht
  have hi : s.im ≠ 0 := by intro h; norm_num [h] at ht
  have hΓ := (hgamma (s/2) (by
    simp only [Complex.div_ofNat_re]
    constructor <;> linarith [hs.1,hs.2])).1
  have hΓ' := hgamma' ((1+s)/2) (by
    simp only [Complex.div_ofNat_re,add_re,one_re]
    constructor <;> linarith [hs.1,hs.2]) (by
    simp only [Complex.div_ofNat_im,add_im,one_im,zero_add,abs_div]
    norm_num
    linarith)
  have hsine : ‖Complex.sin ((Real.pi : ℂ)*((1-s)/2))‖ ≤ Real.exp (Real.pi*|s.im|/2) := by
    have h := complex_sin_norm_le_exp_abs_im ((Real.pi : ℂ)*((1-s)/2))
    convert h using 1
    simp [abs_mul,abs_div]
    ring
  have hpow : ‖(Real.pi : ℂ)^(1/2-s)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi])
    simp only [sub_re,Complex.div_ofNat_re,one_re]
    linarith [hs.1]
  have him : |(s/2).im| = |s.im|/2 := by simp [abs_div]
  have him' : |((1+s)/2).im| = |s.im|/2 := by simp [abs_div]
  rw [him] at hΓ
  rw [him'] at hΓ'
  rw [zetaChi_one_sub_reflection hi,norm_mul,norm_mul,norm_div,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  calc
    _ ≤ 1*(A*(1+|s.im|/2)*Real.exp (-(Real.pi*(|s.im|/2)/2)))*
        ((B*(1+|s.im|/2)^3*Real.exp (-(Real.pi*(|s.im|/2)/2)))*
          Real.exp (Real.pi*|s.im|/2)/Real.pi) := by gcongr
    _ = A*B*(1+|s.im|/2)^4/Real.pi := by
      have he : Real.exp (-(Real.pi*(|s.im|/2)/2))*
          Real.exp (-(Real.pi*(|s.im|/2)/2))*Real.exp (Real.pi*|s.im|/2) = 1 := by
        rw [← Real.exp_add,← Real.exp_add]
        convert Real.exp_zero using 1
        ring
      calc
        _ = A*B*(1+|s.im|/2)^4*
          (Real.exp (-(Real.pi*(|s.im|/2)/2))*Real.exp (-(Real.pi*(|s.im|/2)/2))*
            Real.exp (Real.pi*|s.im|/2))/Real.pi := by ring
        _ = _ := by rw [he,mul_one]
    _ ≤ A*B*(1+|s.im|)^4 := by
      apply (div_le_self (by positivity) (by linarith [Real.two_le_pi])).trans
      gcongr
      linarith [abs_nonneg s.im]

end
end Sechstmoment.Source
