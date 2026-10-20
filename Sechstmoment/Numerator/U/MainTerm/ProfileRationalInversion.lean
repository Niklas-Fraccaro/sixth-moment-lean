import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Sechstmoment.Numerator.U.Diagonal.ProfileHolomorphy


namespace Sechstmoment
open Complex Real MeasureTheory Set
open scoped ContDiff
noncomputable section

theorem a04_vertical_add_norm_lower (c y : ℝ) (A : ℂ) :
    c + A.re ≤ ‖(c : ℂ) + (y : ℂ) * I + A‖ := by
  simpa using Complex.re_le_norm ((c : ℂ) + (y : ℂ) * I + A)

theorem a04_vertical_add_ne_zero (c y : ℝ) (A : ℂ) (hA : 0 < c + A.re) :
    (c : ℂ) + (y : ℂ) * I + A ≠ 0 :=
  norm_pos_iff.mp (hA.trans_le (a04_vertical_add_norm_lower c y A))

theorem profileLaplaceTransform_shifted_onePole_continuous
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (hfc : Continuous f)
    (c t : ℝ) (A : ℂ) (hA : 0 < c + A.re) :
    Continuous (fun y : ℝ => profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I) *
      Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (t : ℂ)) /
        ((c : ℂ) + (y : ℂ) * I + A)) := by
  apply Continuous.div
  · exact ((profileLaplaceTransform_differentiable hf hfc).continuous.comp
      (by fun_prop)).mul (by fun_prop)
  · fun_prop
  · intro y
    exact a04_vertical_add_ne_zero c y A hA

theorem profileLaplaceTransform_shifted_onePole_integrable
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (c t : ℝ) (A : ℂ) (hA : 0 < c + A.re) :
    Integrable (fun y : ℝ => profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I) *
      Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (t : ℂ)) /
        ((c : ℂ) + (y : ℂ) * I + A)) := by
  apply ((profileLaplaceTransform_verticalIntegrable hf hfs c).norm.mul_const
    (Real.exp (-c * t) / (c + A.re))).mono'
  · exact (profileLaplaceTransform_shifted_onePole_continuous hf hfs.continuous c t A hA).aestronglyMeasurable
  · filter_upwards [] with y
    rw [norm_div, norm_mul, Complex.norm_exp]
    have he : (-((c : ℂ) + (y : ℂ) * I) * (t : ℂ)).re = -c * t := by simp
    rw [he]
    calc
      _ ≤ (‖profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I)‖ *
          Real.exp (-c * t)) / (c + A.re) :=
        div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
          hA (a04_vertical_add_norm_lower c y A)
      _ = _ := by ring

theorem profileLaplaceTransform_shifted_twoPole_continuous
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (hfc : Continuous f)
    (c t : ℝ) (A B : ℂ) (hA : 0 < c + A.re) (hB : 0 < c + B.re) :
    Continuous (fun y : ℝ => profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I) *
      Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (t : ℂ)) /
        (((c : ℂ) + (y : ℂ) * I + A) * ((c : ℂ) + (y : ℂ) * I + B))) := by
  apply Continuous.div
  · exact ((profileLaplaceTransform_differentiable hf hfc).continuous.comp
      (by fun_prop)).mul (by fun_prop)
  · fun_prop
  · intro y
    exact mul_ne_zero (a04_vertical_add_ne_zero c y A hA) (a04_vertical_add_ne_zero c y B hB)

theorem profileLaplaceTransform_shifted_twoPole_integrable
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (c t : ℝ) (A B : ℂ) (hA : 0 < c + A.re) (hB : 0 < c + B.re) :
    Integrable (fun y : ℝ => profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I) *
      Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (t : ℂ)) /
        (((c : ℂ) + (y : ℂ) * I + A) * ((c : ℂ) + (y : ℂ) * I + B))) := by
  apply ((profileLaplaceTransform_verticalIntegrable hf hfs c).norm.mul_const
    (Real.exp (-c * t) / ((c + A.re) * (c + B.re)))).mono'
  · exact (profileLaplaceTransform_shifted_twoPole_continuous
      hf hfs.continuous c t A B hA hB).aestronglyMeasurable
  · filter_upwards [] with y
    rw [norm_div, norm_mul, norm_mul, Complex.norm_exp]
    have he : (-((c : ℂ) + (y : ℂ) * I) * (t : ℂ)).re = -c * t := by simp
    rw [he]
    calc
      _ ≤ (‖profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I)‖ *
          Real.exp (-c * t)) / ((c + A.re) * (c + B.re)) := by
        apply div_le_div_of_nonneg_left
          (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le) (mul_pos hA hB)
        exact mul_le_mul (a04_vertical_add_norm_lower c y A)
          (a04_vertical_add_norm_lower c y B) hB.le (norm_nonneg _)
      _ = _ := by ring

theorem profileLaplaceTransform_kernel_pairing
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (c : ℝ) (μ : Measure ℝ) [SFinite μ]
    (h : ℝ → ℂ) (s : ℝ → ℝ) (hh : Continuous h) (hs : Continuous s)
    (hi : Integrable (fun x => ‖h x‖ * Real.exp (-c * s x)) μ) :
    (1 / (2 * π) : ℂ) *
      (∫ y : ℝ, profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I) *
        (∫ x : ℝ, h x * Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (s x : ℂ)) ∂μ)) =
      ∫ x : ℝ, h x * f (s x) ∂μ := by
  let F : ℝ → ℂ := fun y => profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I)
  have hF : Integrable F := profileLaplaceTransform_verticalIntegrable hf hfs c
  have hFc : Continuous F :=
    (profileLaplaceTransform_differentiable hf hfs.continuous).continuous.comp (by fun_prop)
  let K : ℝ × ℝ → ℂ := fun p =>
    F p.1 * (h p.2 * Complex.exp (-((c : ℂ) + (p.1 : ℂ) * I) * (s p.2 : ℂ)))
  have hK : Integrable K (volume.prod μ) := by
    apply (hF.norm.mul_prod hi).mono'
    · exact (show Continuous K by dsimp [K]; fun_prop).aestronglyMeasurable
    · filter_upwards [] with p
      dsimp [K]
      rw [norm_mul, norm_mul, Complex.norm_exp]
      simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.add_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      ring_nf
      exact le_rfl
  have hswap := integral_integral_swap
    (f := fun y x => F y * (h x * Complex.exp
      (-((c : ℂ) + (y : ℂ) * I) * (s x : ℂ)))) hK
  change (1 / (2 * π) : ℂ) *
    (∫ y : ℝ, F y * (∫ x : ℝ, h x *
      Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (s x : ℂ)) ∂μ)) = _
  simp_rw [← integral_const_mul (F _)]
  rw [hswap, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hinner : (∫ y : ℝ, F y * (h x *
      Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (s x : ℂ)))) =
      h x * ∫ y : ℝ, Complex.exp
        (-((c : ℂ) + (y : ℂ) * I) * (s x : ℂ)) * F y := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [hinner]
  calc
    _ = h x * ((1 / (2 * π) : ℂ) * ∫ y : ℝ,
        Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (s x : ℂ)) * F y) := by ring
    _ = h x * f (s x) := by rw [← profileLaplaceTransform_inversion hf hfs c (s x)]

theorem profileLaplaceTransform_shifted_onePole_inversion
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (c t : ℝ) (A : ℂ) (hA : 0 < c + A.re) :
    (1 / (2 * π) : ℂ) *
      (∫ y : ℝ, profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I) *
        Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (t : ℂ)) /
          ((c : ℂ) + (y : ℂ) * I + A)) =
      ∫ x : ℝ in Ioi 0, Complex.exp (-A * (x : ℂ)) * f (x + t) := by
  have hi : Integrable (fun x : ℝ =>
      ‖Complex.exp (-A * (x : ℂ))‖ * Real.exp (-c * (x + t)))
      (volume.restrict (Ioi 0)) := by
    have hbase := (integrableOn_exp_mul_Ioi (a := -(c + A.re)) (by linarith) 0).mul_const
      (Real.exp (-c * t))
    convert hbase using 1
    funext x
    simp only [Complex.norm_exp, neg_mul, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hp := profileLaplaceTransform_kernel_pairing hf hfs c
    (volume.restrict (Ioi 0)) (fun x => Complex.exp (-A * (x : ℂ)))
    (fun x => x + t) (by fun_prop) (by fun_prop) hi
  have hinner (y : ℝ) :
      (∫ x : ℝ in Ioi 0, Complex.exp (-A * (x : ℂ)) *
        Complex.exp (-((c : ℂ) + (y : ℂ) * I) * ((x + t : ℝ) : ℂ))) =
      Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (t : ℂ)) /
        ((c : ℂ) + (y : ℂ) * I + A) := by
    let w : ℂ := (c : ℂ) + (y : ℂ) * I
    have hw : (-(w + A)).re < 0 := by dsimp [w]; simp; linarith
    calc
      _ = Complex.exp (-w * (t : ℂ)) *
          ∫ x : ℝ in Ioi 0, Complex.exp (-(w + A) * (x : ℂ)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with x
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1
        dsimp [w]
        push_cast
        ring
      _ = _ := by
        rw [integral_exp_mul_complex_Ioi hw]
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]
        dsimp [w]
        ring
  simpa only [hinner, mul_div_assoc] using hp

theorem profileLaplaceTransform_shifted_twoPole_inversion
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (c t : ℝ) (A B : ℂ) (hA : 0 < c + A.re) (hB : 0 < c + B.re)
    (hAB : A ≠ B) :
    (1 / (2 * π) : ℂ) *
      (∫ y : ℝ, profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I) *
        Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (t : ℂ)) /
          (((c : ℂ) + (y : ℂ) * I + A) * ((c : ℂ) + (y : ℂ) * I + B))) =
      ∫ x : ℝ in Ioi 0, f (x + t) *
        ((Complex.exp (-A * (x : ℂ)) - Complex.exp (-B * (x : ℂ))) / (B - A)) := by
  let F : ℝ → ℂ := fun y => profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I) *
    Complex.exp (-((c : ℂ) + (y : ℂ) * I) * (t : ℂ))
  let PA : ℝ → ℂ := fun y => F y / ((c : ℂ) + (y : ℂ) * I + A)
  let PB : ℝ → ℂ := fun y => F y / ((c : ℂ) + (y : ℂ) * I + B)
  have hAi : Integrable PA := profileLaplaceTransform_shifted_onePole_integrable hf hfs c t A hA
  have hBi : Integrable PB := profileLaplaceTransform_shifted_onePole_integrable hf hfs c t B hB
  have hpf (y : ℝ) : F y /
      (((c : ℂ) + (y : ℂ) * I + A) * ((c : ℂ) + (y : ℂ) * I + B)) =
      (PA y - PB y) / (B - A) := by
    dsimp [PA, PB]
    field_simp [a04_vertical_add_ne_zero c y A hA,
      a04_vertical_add_ne_zero c y B hB, sub_ne_zero.mpr hAB.symm]
    ring
  have hRA : IntegrableOn (fun x : ℝ => Complex.exp (-A * (x : ℂ)) * f (x + t)) (Ioi 0) := by
    apply Integrable.integrableOn
    apply Continuous.integrable_of_hasCompactSupport
    · exact (by fun_prop : Continuous (fun x : ℝ => Complex.exp (-A * (x : ℂ)))).mul
        (hfs.continuous.comp (by fun_prop))
    · exact (hf.comp_homeomorph (Homeomorph.addRight t)).mul_left
  have hRB : IntegrableOn (fun x : ℝ => Complex.exp (-B * (x : ℂ)) * f (x + t)) (Ioi 0) := by
    apply Integrable.integrableOn
    apply Continuous.integrable_of_hasCompactSupport
    · exact (by fun_prop : Continuous (fun x : ℝ => Complex.exp (-B * (x : ℂ)))).mul
        (hfs.continuous.comp (by fun_prop))
    · exact (hf.comp_homeomorph (Homeomorph.addRight t)).mul_left
  change (1 / (2 * π) : ℂ) * (∫ y : ℝ, F y /
      (((c : ℂ) + (y : ℂ) * I + A) * ((c : ℂ) + (y : ℂ) * I + B))) = _
  simp_rw [hpf]
  rw [integral_div, integral_sub hAi hBi]
  calc
    _ = ((1 / (2 * π) : ℂ) * (∫ y : ℝ, PA y) -
        (1 / (2 * π) : ℂ) * (∫ y : ℝ, PB y)) / (B - A) := by ring
    _ = ((∫ x : ℝ in Ioi 0, Complex.exp (-A * (x : ℂ)) * f (x + t)) -
        (∫ x : ℝ in Ioi 0, Complex.exp (-B * (x : ℂ)) * f (x + t))) / (B - A) := by
      rw [profileLaplaceTransform_shifted_onePole_inversion hf hfs c t A hA,
        profileLaplaceTransform_shifted_onePole_inversion hf hfs c t B hB]
    _ = _ := by
      rw [← integral_sub hRA hRB, ← integral_div]
      apply integral_congr_ae
      filter_upwards [] with x
      ring

theorem profileLaplaceTransform_twoPole_integrable
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (c : ℝ) (A B : ℂ) (hA : 0 < c + A.re) (hB : 0 < c + B.re) :
    Integrable (fun y : ℝ => profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I) /
      (((c : ℂ) + (y : ℂ) * I + A) * ((c : ℂ) + (y : ℂ) * I + B))) := by
  simpa using profileLaplaceTransform_shifted_twoPole_integrable hf hfs c 0 A B hA hB

theorem profileLaplaceTransform_twoPole_continuous
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (hfc : Continuous f)
    (c : ℝ) (A B : ℂ) (hA : 0 < c + A.re) (hB : 0 < c + B.re) :
    Continuous (fun y : ℝ => profileLaplaceTransform f ((c : ℂ) + (y : ℂ) * I) /
      (((c : ℂ) + (y : ℂ) * I + A) * ((c : ℂ) + (y : ℂ) * I + B))) := by
  simpa using profileLaplaceTransform_shifted_twoPole_continuous hf hfc c 0 A B hA hB

end
end Sechstmoment
