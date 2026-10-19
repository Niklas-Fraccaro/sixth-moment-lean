import Mathlib.Analysis.Complex.CauchyIntegral
import Sechstmoment.Numerator.V.Contour.AlmostHolomorphicWeight

/-! Real differentiability and the genuine Cauchy-Green integrand for the
almost-holomorphic weight. The holomorphic factor's derivative cancels;
only the explicitly controlled final Taylor term remains.
-/

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped Topology BigOperators ContDiff
noncomputable section

def almostHolomorphicLift (w : ℝ → ℂ) (K : ℕ) (T : ℝ) (z : ℂ) : ℂ :=
  almostHolomorphicWeight w K T z.re z.im

theorem almostHolomorphicCoefficient_contDiff_lift (T : ℝ) (j : ℕ) :
    ContDiff ℝ 1 (fun z : ℂ => almostHolomorphicCoefficient T z.re j) := by
  unfold almostHolomorphicCoefficient
  have hr : ContDiff ℝ 1 (fun z : ℂ => (z.re : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp Complex.reCLM.contDiff
  have hb : ContDiff ℝ 1 (fun z : ℂ => -I*((z.re : ℂ)-1/2)/(T : ℂ)) :=
    (contDiff_const.mul (hr.sub contDiff_const)).div_const _
  exact (hb.pow j).div_const _

theorem almostHolomorphicLift_contDiff {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (K : ℕ) (T : ℝ) : ContDiff ℝ 1 (almostHolomorphicLift w K T) := by
  unfold almostHolomorphicLift almostHolomorphicWeight
  apply ContDiff.sum
  intro j _
  have hj : ContDiff ℝ 1 (iteratedDeriv j w) := by
    have hfin : ContDiff ℝ ((j+1 : ℕ) : ℕ∞ω) w :=
      hw.of_le (WithTop.coe_le_coe.mpr le_top)
    apply (contDiff_nat_succ_iff_contDiff_one_iteratedDeriv.mp
      hfin).2
  exact (almostHolomorphicCoefficient_contDiff_lift T j).mul
    (hj.comp (Complex.imCLM.contDiff.div_const T))

theorem fderiv_real_direction_eq {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ f z 1 = deriv (fun u : ℝ => f ((u : ℂ)+(z.im : ℂ)*I)) z.re := by
  have hp : HasDerivAt (fun u : ℝ => (u : ℂ)+(z.im : ℂ)*I) 1 z.re := by
    simpa only [id_eq] using ((hasDerivAt_id (z.re : ℂ)).comp_ofReal.add_const ((z.im : ℂ)*I))
  have hf' : HasFDerivAt f (fderiv ℝ f z) ((z.re : ℂ)+(z.im : ℂ)*I) := by
    rw [Complex.re_add_im]
    exact hf.hasFDerivAt
  have h := hf'.comp_hasDerivAt z.re hp
  simpa only [Function.comp_def,Complex.re_add_im] using h.deriv.symm

theorem fderiv_imag_direction_eq {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    fderiv ℝ f z I = deriv (fun t : ℝ => f ((z.re : ℂ)+(t : ℂ)*I)) z.im := by
  have hp : HasDerivAt (fun t : ℝ => (z.re : ℂ)+(t : ℂ)*I) I z.im := by
    simpa only [id_eq,one_mul] using
      (((hasDerivAt_id (z.im : ℂ)).comp_ofReal.mul_const I).const_add (z.re : ℂ))
  have hf' : HasFDerivAt f (fderiv ℝ f z) ((z.re : ℂ)+(z.im : ℂ)*I) := by
    rw [Complex.re_add_im]
    exact hf.hasFDerivAt
  have h := hf'.comp_hasDerivAt z.im hp
  simpa only [Function.comp_def,Complex.re_add_im] using h.deriv.symm

theorem holomorphic_hasDerivAt_horizontal {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) :
    HasDerivAt (fun u : ℝ => F ((u : ℂ)+(z.im : ℂ)*I)) (deriv F z) z.re := by
  have hp : HasDerivAt (fun u : ℂ => u+(z.im : ℂ)*I) 1 (z.re : ℂ) :=
    (hasDerivAt_id _).add_const _
  have h := hF.hasDerivAt.comp_of_eq (z.re : ℂ) hp (Complex.re_add_im z).symm
  simpa only [Function.comp_def,mul_one] using h.comp_ofReal

theorem holomorphic_hasDerivAt_vertical {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) :
    HasDerivAt (fun t : ℝ => F ((z.re : ℂ)+(t : ℂ)*I)) ((deriv F z)*I) z.im := by
  have hp : HasDerivAt (fun t : ℂ => (z.re : ℂ)+t*I) I (z.im : ℂ) := by
    simpa only [id_eq,one_mul] using ((hasDerivAt_id _).mul_const I).const_add (z.re : ℂ)
  have h := hF.hasDerivAt.comp_of_eq (z.im : ℂ) hp (Complex.re_add_im z).symm
  simpa only [Function.comp_def] using h.comp_ofReal

theorem almostHolomorphic_product_cauchyGreen {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (K : ℕ) (T : ℝ) {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℂ F z) :
    I*fderiv ℝ (fun v => F v*almostHolomorphicLift w K T v) z 1-
      fderiv ℝ (fun v => F v*almostHolomorphicLift w K T v) z I =
      I*F z*((I/(T : ℂ))*almostHolomorphicCoefficient T z.re K*
        iteratedDeriv (K+1) w (z.im/T)) := by
  have hW := (almostHolomorphicLift_contDiff hw K T).differentiable (by norm_num) z
  have hf : DifferentiableAt ℝ (fun v => F v*almostHolomorphicLift w K T v) z :=
    (hF.restrictScalars ℝ).mul hW
  rw [fderiv_real_direction_eq hf,fderiv_imag_direction_eq hf]
  have hu := (holomorphic_hasDerivAt_horizontal hF).fun_mul
    (almostHolomorphicWeight_hasDerivAt_real w K T z.re z.im)
  have ht := (holomorphic_hasDerivAt_vertical hF).fun_mul
    (almostHolomorphicWeight_hasDerivAt_imag hw K T z.re z.im)
  have hueq : (fun u : ℝ => F ((u : ℂ)+(z.im : ℂ)*I)*
      almostHolomorphicLift w K T ((u : ℂ)+(z.im : ℂ)*I)) =
      (fun u : ℝ => F ((u : ℂ)+(z.im : ℂ)*I)*almostHolomorphicWeight w K T u z.im) := by
    ext u
    simp [almostHolomorphicLift]
  have hteq : (fun t : ℝ => F ((z.re : ℂ)+(t : ℂ)*I)*
      almostHolomorphicLift w K T ((z.re : ℂ)+(t : ℂ)*I)) =
      (fun t : ℝ => F ((z.re : ℂ)+(t : ℂ)*I)*almostHolomorphicWeight w K T z.re t) := by
    ext t
    simp [almostHolomorphicLift]
  rw [hueq,hteq,hu.deriv,ht.deriv]
  simp only [Complex.re_add_im]
  rw [Finset.sum_range_succ]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem almostHolomorphic_rectangle_identity {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (K : ℕ) (T a b A B : ℝ) (F : ℂ → ℂ)
    (hF : ∀ z ∈ uIcc a b ×ℂ uIcc A B, DifferentiableAt ℂ F z) :
    (∫ u in a..b, F ((u : ℂ)+(A : ℂ)*I)*almostHolomorphicWeight w K T u A)-
    (∫ u in a..b, F ((u : ℂ)+(B : ℂ)*I)*almostHolomorphicWeight w K T u B)+
    I*(∫ t in A..B, F ((b : ℂ)+(t : ℂ)*I)*almostHolomorphicWeight w K T b t)-
    I*(∫ t in A..B, F ((a : ℂ)+(t : ℂ)*I)*almostHolomorphicWeight w K T a t) =
    ∫ u in a..b, ∫ t in A..B, I*F ((u : ℂ)+(t : ℂ)*I)*
      ((I/(T : ℂ))*almostHolomorphicCoefficient T u K*iteratedDeriv (K+1) w (t/T)) := by
  let G : ℂ → ℂ := fun z => F z*almostHolomorphicLift w K T z
  let R : Set ℂ := uIcc a b ×ℂ uIcc A B
  have hW := (almostHolomorphicLift_contDiff hw K T).differentiable (by norm_num)
  have hd : DifferentiableOn ℝ G R := by
    intro z hz
    exact (((hF z hz).restrictScalars ℝ).mul (hW z)).differentiableWithinAt
  have hFc : ContinuousOn F R := fun z hz => (hF z hz).continuousAt.continuousWithinAt
  have hD : Continuous (fun z : ℂ =>
      (I/(T : ℂ))*almostHolomorphicCoefficient T z.re K*iteratedDeriv (K+1) w (z.im/T)) :=
    ((almostHolomorphicCoefficient_contDiff_lift T K).continuous.const_mul _).mul
      ((hw.continuous_iteratedDeriv (K+1) (WithTop.coe_le_coe.mpr le_top)).comp
        (Complex.continuous_im.div_const T))
  have hc : ContinuousOn (fun z : ℂ => I*F z*
      ((I/(T : ℂ))*almostHolomorphicCoefficient T z.re K*iteratedDeriv (K+1) w (z.im/T))) R :=
    (hFc.const_mul I).mul hD.continuousOn
  have hrect : IsCompact R := isCompact_uIcc.reProdIm isCompact_uIcc
  have he (z : ℂ) (hz : z ∈ R) :
      I*fderiv ℝ G z 1-fderiv ℝ G z I = I*F z*
        ((I/(T : ℂ))*almostHolomorphicCoefficient T z.re K*iteratedDeriv (K+1) w (z.im/T)) :=
    almostHolomorphic_product_cauchyGreen hw K T (hF z hz)
  have hi : IntegrableOn (fun z => I • fderiv ℝ G z 1-fderiv ℝ G z I) R :=
    (hc.integrableOn_compact hrect).congr_fun
      (fun z hz => by simpa only [smul_eq_mul] using (he z hz).symm) hrect.measurableSet
  have h := Complex.integral_boundary_rect_of_differentiableOn_real G
    ((a : ℂ)+(A : ℂ)*I) ((b : ℂ)+(B : ℂ)*I)
    (by simpa using hd) (by simpa using hi)
  calc
    _ = ∫ u in a..b, ∫ t in A..B,
        I*fderiv ℝ G ((u : ℂ)+(t : ℂ)*I) 1-fderiv ℝ G ((u : ℂ)+(t : ℂ)*I) I := by
      simpa [G,almostHolomorphicLift,smul_eq_mul] using h
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u hu
      apply intervalIntegral.integral_congr
      intro t ht
      simpa using he ((u : ℂ)+(t : ℂ)*I) (by
        constructor
        · simpa using hu
        · simpa using ht)

theorem almostHolomorphic_vertical_shift {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (K : ℕ) {T : ℝ} (hT : 0 < T)
    (c : ℝ) (F : ℂ → ℂ)
    (hF : ∀ z ∈ uIcc (1/2 : ℝ) c ×ℂ uIcc (T/2) (3*T), DifferentiableAt ℂ F z) :
    (∫ t in T/2..3*T, F ((c : ℂ)+(t : ℂ)*I)*almostHolomorphicWeight w K T c t)-
      (∫ t in T/2..3*T, F ((1/2 : ℂ)+(t : ℂ)*I)*w (t/T)) =
      ∫ u in (1/2 : ℝ)..c, ∫ t in T/2..3*T, F ((u : ℂ)+(t : ℂ)*I)*
        ((I/(T : ℂ))*almostHolomorphicCoefficient T u K*iteratedDeriv (K+1) w (t/T)) := by
  have h := almostHolomorphic_rectangle_identity hw K T (1/2) c (T/2) (3*T) F hF
  have hbot (u : ℝ) : almostHolomorphicWeight w K T u (T/2) = 0 :=
    almostHolomorphicWeight_eq_zero_outside_dyadic hws K hT u (T/2) (by
      intro h; linarith [h.1])
  have htop (u : ℝ) : almostHolomorphicWeight w K T u (3*T) = 0 :=
    almostHolomorphicWeight_eq_zero_outside_dyadic hws K hT u (3*T) (by
      intro h; linarith [h.2])
  simp only [hbot,htop,mul_zero,intervalIntegral.integral_zero,sub_self,zero_add,
    almostHolomorphicWeight_left_boundary] at h
  simp_rw [mul_assoc,intervalIntegral.integral_const_mul] at h
  apply mul_left_cancel₀ I_ne_zero
  simpa [mul_sub,mul_assoc] using h

theorem almostHolomorphic_vertical_shift_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (K : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ T : ℝ, 0 < T → ∀ c : ℝ, c ∈ Icc (1/2 : ℝ) (3/2) →
      ∀ F : ℂ → ℂ,
      (∀ z ∈ Icc (1/2 : ℝ) c ×ℂ Icc (T/2) (3*T), DifferentiableAt ℂ F z) →
      ∀ M : ℝ, 0 ≤ M → (∀ z ∈ Icc (1/2 : ℝ) c ×ℂ Icc (T/2) (3*T), ‖F z‖ ≤ M) →
      ‖(∫ t in T/2..3*T, F ((c : ℂ)+(t : ℂ)*I)*almostHolomorphicWeight w K T c t)-
        (∫ t in T/2..3*T, F ((1/2 : ℂ)+(t : ℂ)*I)*w (t/T))‖ ≤
        (c-1/2)*(3*T)*M*D/T^(K+1) := by
  obtain ⟨D,hD,hdefect⟩ := almostHolomorphicWeight_defect_bound hw hws K
  refine ⟨D,hD,?_⟩
  intro T hT c hc F hF M hM hbound
  have hT0 : T/2 ≤ 3*T := by linarith
  rw [almostHolomorphic_vertical_shift hw hws K hT c F (by
    simpa only [uIcc_of_le hc.1,uIcc_of_le hT0] using hF)]
  have hpoint (u t : ℝ) (hu : u ∈ Icc (1/2 : ℝ) c) (ht : t ∈ Icc (T/2) (3*T)) :
      ‖F ((u : ℂ)+(t : ℂ)*I)*
        ((I/(T : ℂ))*almostHolomorphicCoefficient T u K*iteratedDeriv (K+1) w (t/T))‖ ≤
        M*(D/T^(K+1)) := by
    rw [norm_mul,← almostHolomorphicWeight_cauchyRiemann_defect hw]
    apply mul_le_mul
    · exact hbound _ ⟨by simpa using hu,by simpa using ht⟩
    · apply hdefect T hT u t
      rw [abs_of_nonneg (by linarith [hu.1])]
      linarith [hu.2,hc.2]
    · exact norm_nonneg _
    · exact hM
  have hinner (u : ℝ) (hu : u ∈ uIoc (1/2 : ℝ) c) :
      ‖∫ t in T/2..3*T, F ((u : ℂ)+(t : ℂ)*I)*
        ((I/(T : ℂ))*almostHolomorphicCoefficient T u K*iteratedDeriv (K+1) w (t/T))‖ ≤
        (3*T)*(M*(D/T^(K+1))) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht =>
      hpoint u t (by rw [uIoc_of_le hc.1] at hu; exact ⟨hu.1.le,hu.2⟩)
        (by rw [uIoc_of_le hT0] at ht; exact ⟨ht.1.le,ht.2⟩))
    rw [abs_of_nonneg (sub_nonneg.mpr hT0)] at h
    exact h.trans (by
      have hp : 0 ≤ M*(D/T^(K+1)) := by positivity
      nlinarith)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hinner
  rw [abs_of_nonneg (sub_nonneg.mpr hc.1)] at h
  convert h using 1
  ring

theorem almostHolomorphicWeight_integral_eq_interval {w : ℝ → ℂ}
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (K : ℕ) {T : ℝ} (hT : 0 < T)
    (u : ℝ) (F : ℝ → ℂ) :
    (∫ t : ℝ, F t*almostHolomorphicWeight w K T u t) =
      ∫ t in T/2..3*T, F t*almostHolomorphicWeight w K T u t := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  have hW : almostHolomorphicWeight w K T u t ≠ 0 := by
    intro h
    apply ht
    change F t*almostHolomorphicWeight w K T u t = 0
    rw [h,mul_zero]
  have hinside : t ∈ Icc T (2*T) := by
    by_contra h
    exact hW (almostHolomorphicWeight_eq_zero_outside_dyadic hws K hT u t h)
  exact ⟨by linarith [hinside.1],by linarith [hinside.2]⟩

end
end Sechstmoment.Source
