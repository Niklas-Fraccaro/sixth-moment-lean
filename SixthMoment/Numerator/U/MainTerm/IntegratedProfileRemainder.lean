import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import SixthMoment.Numerator.Polar.Mellin.ContourUniform
import SixthMoment.Numerator.U.Diagonal.ActualProfileMellin
import SixthMoment.Numerator.U.Diagonal.ProfileHolomorphy


namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff FourierTransform
open Classical
noncomputable section
set_option maxHeartbeats 0

private theorem entangled_profile_continuous {α : MomentShifts} {δ c : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (hc : -δ/2 ≤ c) :
    Continuous (fun w : (ℝ × ℝ) × ℝ => polarArithmeticEntangledFactor α
      ((δ:ℂ)+(w.1.1:ℂ)*I) ((δ:ℂ)+(w.1.2:ℂ)*I) ((c:ℂ)+(w.2:ℂ)*I)) := by
  rw [continuous_iff_continuousAt]
  intro w
  let u : ℂ := (δ:ℂ)+(w.1.1:ℂ)*I
  let v : ℂ := (δ:ℂ)+(w.1.2:ℂ)*I
  let z : ℂ := (c:ℂ)+(w.2:ℂ)*I
  have hu : δ ≤ u.re := by simp [u]
  have hv : δ ≤ v.re := by simp [v]
  have hz : -δ/2 ≤ z.re := by simpa [z] using hc
  obtain ⟨ha,hb⟩ := polarMellinTriples_re_lower_bound hδ hα hu hv hz
  have hmap : Continuous (fun w : (ℝ × ℝ) × ℝ =>
      (polarMellinLeftTriple α ((δ:ℂ)+(w.1.1:ℂ)*I) ((c:ℂ)+(w.2:ℂ)*I),
       polarMellinRightTriple α ((δ:ℂ)+(w.1.2:ℂ)*I) ((c:ℂ)+(w.2:ℂ)*I))) := by
    unfold polarMellinLeftTriple polarMellinRightTriple
    fun_prop
  have hA : ContinuousAt (fun w : (ℝ × ℝ) × ℝ =>
      shiftedPolarEulerRest (polarMellinLeftTriple α ((δ:ℂ)+(w.1.1:ℂ)*I) ((c:ℂ)+(w.2:ℂ)*I))
        (polarMellinRightTriple α ((δ:ℂ)+(w.1.2:ℂ)*I) ((c:ℂ)+(w.2:ℂ)*I))) w :=
    ContinuousAt.comp (f := fun w : (ℝ × ℝ) × ℝ =>
      (polarMellinLeftTriple α ((δ:ℂ)+(w.1.1:ℂ)*I) ((c:ℂ)+(w.2:ℂ)*I),
       polarMellinRightTriple α ((δ:ℂ)+(w.1.2:ℂ)*I) ((c:ℂ)+(w.2:ℂ)*I)))
      (g := fun ab : PolarShiftSpace => shiftedPolarEulerRest ab.1 ab.2)
      ((shiftedPolarEulerRest_continuousOn hδ1).continuousAt
        ((polarShiftDomain_isOpen δ).mem_nhds (show
          (polarMellinLeftTriple α u z,polarMellinRightTriple α v z) ∈
            polarShiftDomain δ from ⟨ha,hb⟩))) hmap.continuousAt
  have hZ : ContinuousAt (fun w : (ℝ × ℝ) × ℝ => polarEntangledZetaProduct α
      ((δ:ℂ)+(w.1.1:ℂ)*I) ((δ:ℂ)+(w.1.2:ℂ)*I) ((c:ℂ)+(w.2:ℂ)*I)) w := by
    unfold polarEntangledZetaProduct
    apply tendsto_finsetProd
    intro i _
    have hne : polarEntangledZetaArguments α u v z i ≠ 1 := by
      intro he
      have hr := polarEntangledZetaArguments_re_lower_bound hδ hα hu hv hz i
      rw [he,one_re] at hr
      linarith
    have hi : ContinuousAt (fun w : (ℝ × ℝ) × ℝ => polarEntangledZetaArguments α
        ((δ:ℂ)+(w.1.1:ℂ)*I) ((δ:ℂ)+(w.1.2:ℂ)*I) ((c:ℂ)+(w.2:ℂ)*I) i) w := by
      unfold polarEntangledZetaArguments
      fin_cases i <;> fun_prop
    exact ContinuousAt.comp (f := fun w : (ℝ × ℝ) × ℝ => polarEntangledZetaArguments α
      ((δ:ℂ)+(w.1.1:ℂ)*I) ((δ:ℂ)+(w.1.2:ℂ)*I) ((c:ℂ)+(w.2:ℂ)*I) i)
      (g := riemannZeta) (differentiableAt_riemannZeta hne).continuousAt hi
  exact hA.mul hZ

def actualProfileTransformProduct (f g : ℝ → ℂ) (L δ : ℝ) (y : ℝ × ℝ) : ℂ :=
  actualProfileTransformLine f L δ y.1*actualProfileTransformLine g L δ y.2

theorem actualProfileTransformProduct_integrable {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {L : ℝ} (hL : 0 < L) (δ : ℝ) :
    Integrable (actualProfileTransformProduct f g L δ) (volume.prod volume) :=
  (actualProfileTransformLine_integrable hf hfs hL δ).mul_prod
    (actualProfileTransformLine_integrable hg hgs hL δ)

theorem actualProfileLeftRemainderKernel_integrable
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {L δ x : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hx : 0 < x)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    Integrable (fun w : (ℝ × ℝ) × ℝ => actualProfileTransformProduct f g L δ w.1*
      (polarMellinArithmeticKernel T σ m ((δ:ℂ)+(w.1.1:ℂ)*I)
        ((δ:ℂ)+(w.1.2:ℂ)*I) ((-δ/2:ℝ)+(w.2:ℂ)*I)/
          ((-δ/2:ℝ)+(w.2:ℂ)*I)*(x:ℂ)^(2*((-δ/2:ℝ)+(w.2:ℂ)*I))))
      ((volume.prod volume).prod volume) := by
  have hshift (j : Fin 4) : ‖bblrSixShifts (rawMomentShifts T σ) m j‖ ≤ δ/4 :=
    bblrSixShifts_norm_le _ hα m j
  have hz : Continuous (fun s : ℝ => ((-δ/2:ℝ)+(s:ℂ)*I : ℂ)) := by fun_prop
  have hzne (s : ℝ) : ((-δ/2:ℝ)+(s:ℂ)*I : ℂ) ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
    linarith
  have hw : Continuous (fun s : ℝ =>
      (((-δ/2:ℝ)+(s:ℂ)*I):ℂ)⁻¹*(x:ℂ)^(2*((-δ/2:ℝ)+(s:ℂ)*I))) :=
    (hz.inv₀ hzne).mul ((hz.const_mul (2:ℂ)).const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hx.ne')))
  have hcore := (polarPureLeftContour_integrable T σ m hδ (by linarith)
      (fun ij => purePolarRoot_norm_le_of_rawShifts hα (m,ij))).mul_bdd
    hw.aestronglyMeasurable
    (Eventually.of_forall (polarMellinScaleWeight_left_norm_bound hδ hx))
  have hprod := (actualProfileTransformProduct_integrable hf hfs hg hgs hL δ).mul_prod hcore
  have hi := hprod.mul_bdd
    (entangled_profile_continuous hδ hδ1 hshift (le_refl (-δ/2))).aestronglyMeasurable
    (Eventually.of_forall (fun w : (ℝ × ℝ) × ℝ =>
      polarArithmeticEntangledFactor_norm_bound hδ hδ1 hshift
        (u := (δ:ℂ)+(w.1.1:ℂ)*I) (v := (δ:ℂ)+(w.1.2:ℂ)*I)
        (z := (-δ/2:ℝ)+(w.2:ℂ)*I) (by simp) (by simp) (by simp)))
  convert hi using 1
  funext w
  unfold polarMellinArithmeticKernel
  simp only [div_eq_mul_inv]
  ring

theorem actualProfileRemainder_integrable
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {L δ x : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hx : 0 < x)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    Integrable (fun y : ℝ × ℝ => actualProfileTransformProduct f g L δ y*
      polarMellinRemainderIntegral T σ m ((δ:ℂ)+(y.1:ℂ)*I)
        ((δ:ℂ)+(y.2:ℂ)*I) x δ) (volume.prod volume) := by
  have hi := (actualProfileLeftRemainderKernel_integrable T σ m hL hδ hδ1 hx
    hα hf hfs hg hgs).integral_prod_left.const_mul (1/(2*π):ℂ)
  convert hi using 1
  funext y
  unfold polarMellinRemainderIntegral verticalIntegral
  dsimp only
  rw [integral_const_mul]
  ring

theorem actualProfilePrincipal_integrable
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {L δ : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    Integrable (fun y : ℝ × ℝ => actualProfileTransformProduct f g L δ y*
      polarMellinRemovedKernel T σ m ((δ:ℂ)+(y.1:ℂ)*I)
        ((δ:ℂ)+(y.2:ℂ)*I) 0) (volume.prod volume) := by
  have hshift (j : Fin 4) : ‖bblrSixShifts (rawMomentShifts T σ) m j‖ ≤ δ/4 :=
    bblrSixShifts_norm_le _ hα m j
  have hA : Continuous (fun y : ℝ × ℝ => polarArithmeticEntangledFactor
      (bblrSixShifts (rawMomentShifts T σ) m)
      ((δ:ℂ)+(y.1:ℂ)*I) ((δ:ℂ)+(y.2:ℂ)*I) 0) := by
    have h := (entangled_profile_continuous hδ hδ1 hshift
      (c := 0) (by linarith)).comp (show Continuous (fun y : ℝ × ℝ => (y,(0:ℝ))) by fun_prop)
    convert h using 1
    funext y
    simp
  have hi := ((actualProfileTransformProduct_integrable hf hfs hg hgs hL δ).mul_bdd
    hA.aestronglyMeasurable (Eventually.of_forall (fun y : ℝ × ℝ =>
      polarArithmeticEntangledFactor_norm_bound hδ hδ1 hshift
        (u := (δ:ℂ)+(y.1:ℂ)*I) (v := (δ:ℂ)+(y.2:ℂ)*I) (z := 0)
        (by simp) (by simp) (by simp; linarith)))).mul_const (purePolarZetaProduct T σ m 0)
  convert hi using 1
  funext y
  rw [polarMellinRemovedKernel_zero T σ m _ _ hρ]
  ring

theorem actualProfilePrincipal_add_remainder_integral
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {L δ x : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hx : 0 < x)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    (∫ y : ℝ × ℝ, actualProfileTransformProduct f g L δ y*
      (polarMellinRemovedKernel T σ m ((δ:ℂ)+(y.1:ℂ)*I) ((δ:ℂ)+(y.2:ℂ)*I) 0+
        polarMellinRemainderIntegral T σ m ((δ:ℂ)+(y.1:ℂ)*I)
          ((δ:ℂ)+(y.2:ℂ)*I) x δ) ∂(volume.prod volume)) =
      (∫ y : ℝ × ℝ, actualProfileTransformProduct f g L δ y*
        polarMellinRemovedKernel T σ m ((δ:ℂ)+(y.1:ℂ)*I)
          ((δ:ℂ)+(y.2:ℂ)*I) 0 ∂(volume.prod volume))+
      (∫ y : ℝ × ℝ, actualProfileTransformProduct f g L δ y*
        polarMellinRemainderIntegral T σ m ((δ:ℂ)+(y.1:ℂ)*I)
          ((δ:ℂ)+(y.2:ℂ)*I) x δ ∂(volume.prod volume)) := by
  simp_rw [mul_add]
  exact integral_add
    (actualProfilePrincipal_integrable T σ m hL hδ hδ1 hα hρ hf hfs hg hgs)
    (actualProfileRemainder_integrable T σ m hL hδ hδ1 hx hα hf hfs hg hgs)

def actualIntegratedProfileRemainder (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (f g : ℝ → ℂ) (L δ x : ℝ) : ℂ :=
  ((L:ℂ)/(2*π))^2 * ∫ y : ℝ × ℝ, actualProfileTransformProduct f g L δ y*
    polarMellinRemainderIntegral T σ m ((δ:ℂ)+(y.1:ℂ)*I)
      ((δ:ℂ)+(y.2:ℂ)*I) x δ ∂(volume.prod volume)

theorem actualIntegratedProfileRemainder_uniform_log_bound {δ κ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ), 1 < T → 1 ≤ Real.log T →
      ∀ σ : MomentShifts,
      (∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖) →
      (∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4) →
      ∀ (m : Fin 6) (f g : ℝ → ℂ), HasCompactSupport f → ContDiff ℝ ∞ f →
      HasCompactSupport g → ContDiff ℝ ∞ g → ∀ L : ℝ, 0 < L → ∀ x : ℝ, 0 < x →
        ‖actualIntegratedProfileRemainder T σ m f g L δ x‖ ≤
          (L/(2*π))^2*(C*(Real.log T)^48*x^(-δ))*
            ((∫ y : ℝ, ‖actualProfileTransformLine f L δ y‖)*
              (∫ y : ℝ, ‖actualProfileTransformLine g L δ y‖)) := by
  obtain ⟨C,hC,hB⟩ := polarMellinRemainderIntegral_uniform_log_bound hδ hδ1 hκ
  refine ⟨C,hC,?_⟩
  intro T hT hlog σ hgap hα m f g hf hfs hg hgs L hL x hx
  have hprod := actualProfileTransformProduct_integrable hf hfs hg hgs hL δ
  have hb := norm_integral_le_of_norm_le
    (f := fun y : ℝ × ℝ => actualProfileTransformProduct f g L δ y*
      polarMellinRemainderIntegral T σ m ((δ:ℂ)+(y.1:ℂ)*I)
        ((δ:ℂ)+(y.2:ℂ)*I) x δ)
    (hprod.norm.mul_const (C*(Real.log T)^48*x^(-δ)))
    (Eventually.of_forall (fun y : ℝ × ℝ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB T hT hlog σ hgap hα m
        ((δ:ℂ)+(y.1:ℂ)*I) ((δ:ℂ)+(y.2:ℂ)*I) (by simp) (by simp) x hx)
        (norm_nonneg _)))
  rw [integral_mul_const] at hb
  have hn : (∫ y : ℝ × ℝ, ‖actualProfileTransformProduct f g L δ y‖
      ∂(volume.prod volume)) =
      (∫ y : ℝ, ‖actualProfileTransformLine f L δ y‖)*
      (∫ y : ℝ, ‖actualProfileTransformLine g L δ y‖) := by
    unfold actualProfileTransformProduct
    simp_rw [norm_mul]
    exact integral_prod_mul (fun y : ℝ => ‖actualProfileTransformLine f L δ y‖)
      (fun y : ℝ => ‖actualProfileTransformLine g L δ y‖)
  rw [hn] at hb
  unfold actualIntegratedProfileRemainder
  rw [norm_mul,norm_pow,norm_div,Complex.norm_real,Real.norm_of_nonneg hL.le]
  have hp : ‖(2*π:ℂ)‖ = 2*π := by
    rw [norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_of_nonneg pi_pos.le]
  rw [hp]
  exact (mul_le_mul_of_nonneg_left hb (sq_nonneg (L/(2*π)))).trans_eq (by ring)

private theorem profile_weight_deriv {f : ℝ → ℂ} (hfs : ContDiff ℝ ∞ f) (c x : ℝ) :
    deriv (profileExponentialWeight f c) x =
      (Real.exp (c*x):ℂ)*((c:ℂ)*f x+deriv f x) := by
  have he := ((Real.hasDerivAt_exp (c*x)).comp x ((hasDerivAt_id x).const_mul c)).ofReal_comp
  have hf := (hfs.differentiable (by simp) x).hasDerivAt
  have h := he.mul hf
  have hd : deriv (profileExponentialWeight f c) x =
      ((Real.exp (c*x)*c:ℝ):ℂ)*f x+(Real.exp (c*x):ℂ)*deriv f x := by
    simpa only [profileExponentialWeight,Function.comp_apply,id_eq,mul_one] using! h.deriv
  rw [hd]
  push_cast
  ring

private theorem profile_weight_deriv_two {f : ℝ → ℂ} (hfs : ContDiff ℝ ∞ f) (c x : ℝ) :
    deriv (deriv (profileExponentialWeight f c)) x =
      (Real.exp (c*x):ℂ)*((c:ℂ)^2*f x+2*(c:ℂ)*deriv f x+deriv (deriv f) x) := by
  have hfd : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hfs).2
  let q : ℝ → ℂ := fun y => (c:ℂ)*f y+deriv f y
  have hq : ContDiff ℝ ∞ q := (contDiff_const.mul hfs).add hfd
  have hqder : deriv q x = (c:ℂ)*deriv f x+deriv (deriv f) x := by
    exact (((hfs.differentiable (by simp) x).hasDerivAt.const_mul (c:ℂ)).add
      ((hfd.differentiable (by simp) x).hasDerivAt)).deriv
  have heq : deriv (profileExponentialWeight f c) = profileExponentialWeight q c :=
    funext (profile_weight_deriv hfs c)
  rw [heq,profile_weight_deriv hq,hqder]
  dsimp [q]
  ring

private theorem fourier_norm_le_L1 (f : ℝ → ℂ) (v : ℝ) :
    ‖𝓕 f v‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  rw [Real.fourier_eq']
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with x
  rw [norm_smul,Complex.norm_exp]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_zero,Real.exp_zero,one_mul]

theorem profileLaplaceTransform_L1_endpoint_bound {f : ℝ → ℂ} {a : ℝ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ Iic a) {c : ℝ} (hc : 0 ≤ c) :
    (∫ v : ℝ, ‖profileLaplaceTransform f ((c:ℂ)+(v:ℂ)*I)‖) ≤
      Real.exp (c*a)*((1+c)^2)*
        ((∫ x : ℝ, ‖f x‖+2*‖deriv f x‖+‖deriv (deriv f) x‖)*
          (∫ v : ℝ, (1+v^2)⁻¹)) := by
  let q := profileExponentialWeight f c
  have hqK := profileExponentialWeight_hasCompactSupport hf c
  have hqC := profileExponentialWeight_contDiff hfs c
  have hqdC : ContDiff ℝ ∞ (deriv q) := (contDiff_infty_iff_deriv.mp hqC).2
  have hfdC : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hfs).2
  have hfddC : ContDiff ℝ ∞ (deriv (deriv f)) := (contDiff_infty_iff_deriv.mp hfdC).2
  have hqI : Integrable q := hqC.continuous.integrable_of_hasCompactSupport hqK
  have hqdI : Integrable (deriv q) := hqdC.continuous.integrable_of_hasCompactSupport hqK.deriv
  have hqddI : Integrable (deriv (deriv q)) :=
    (contDiff_infty_iff_deriv.mp hqdC).2.continuous.integrable_of_hasCompactSupport hqK.deriv.deriv
  have hfI : Integrable f := hfs.continuous.integrable_of_hasCompactSupport hf
  have hfdI : Integrable (deriv f) := hfdC.continuous.integrable_of_hasCompactSupport hf.deriv
  have hfddI : Integrable (deriv (deriv f)) :=
    hfddC.continuous.integrable_of_hasCompactSupport hf.deriv.deriv
  let H : ℝ → ℝ := fun x => ‖f x‖+2*‖deriv f x‖+‖deriv (deriv f) x‖
  have hHI : Integrable H := (hfI.norm.add (hfdI.norm.const_mul 2)).add hfddI.norm
  have hH0 : 0 ≤ ∫ x : ℝ, H x := integral_nonneg (fun x => by dsimp [H]; positivity)
  have hpoint (x : ℝ) : ‖q x‖+‖deriv (deriv q) x‖ ≤ Real.exp (c*a)*(1+c)^2*H x := by
    by_cases hx : x ∈ tsupport f
    · have hxa : x ≤ a := hsupp hx
      have he : Real.exp (c*x) ≤ Real.exp (c*a) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hxa hc)
      have hd := profile_weight_deriv_two hfs c x
      change deriv (deriv q) x = _ at hd
      rw [hd]
      have hdn : ‖(c:ℂ)^2*f x+2*(c:ℂ)*deriv f x+deriv (deriv f) x‖ ≤
          c^2*‖f x‖+2*c*‖deriv f x‖+‖deriv (deriv f) x‖ := by
        apply (norm_add_le _ _).trans
        apply add_le_add
        · apply (norm_add_le _ _).trans_eq
          simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hc,
            Complex.norm_ofNat]
        · rfl
      have hqn : ‖q x‖ = Real.exp (c*x)*‖f x‖ := by
        dsimp [q,profileExponentialWeight]
        rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
      rw [hqn,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
      calc
        _ ≤ Real.exp (c*x)*(‖f x‖+(c^2*‖f x‖+2*c*‖deriv f x‖+‖deriv (deriv f) x‖)) := by
          nlinarith [mul_le_mul_of_nonneg_left hdn (Real.exp_pos (c*x)).le]
        _ ≤ Real.exp (c*a)*(‖f x‖+(c^2*‖f x‖+2*c*‖deriv f x‖+‖deriv (deriv f) x‖)) := by
          gcongr
        _ ≤ _ := by
          simp only [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
          dsimp [H]
          nlinarith [norm_nonneg (f x),norm_nonneg (deriv f x),norm_nonneg (deriv (deriv f) x),
            mul_nonneg hc (norm_nonneg (f x)),mul_nonneg (sq_nonneg c) (norm_nonneg (deriv f x)),
            mul_nonneg hc (norm_nonneg (deriv (deriv f) x)),
            mul_nonneg (sq_nonneg c) (norm_nonneg (deriv (deriv f) x))]
    · have hfx : f x=0 := Function.notMem_support.mp (fun h => hx (subset_tsupport f h))
      have hdx : deriv f x=0 := deriv_of_notMem_tsupport hx
      have hddx : deriv (deriv f) x=0 := deriv_of_notMem_tsupport
        (fun hx' => hx (tsupport_deriv_subset hx'))
      have hqx : q x=0 := by simp [q,profileExponentialWeight,hfx]
      have hqddx : deriv (deriv q) x=0 := by
        change deriv (deriv (profileExponentialWeight f c)) x=0
        simp [profile_weight_deriv_two hfs,hfx,hdx,hddx]
      simp [hqx,hqddx,H,hfx,hdx,hddx]
  have hcoeff (v : ℝ) : (2*π*I*((-v/(2*π):ℝ):ℂ):ℂ)=-(v:ℂ)*I := by
    push_cast
    field_simp
  have hnorm (v : ℝ) : v^2*‖𝓕 q (-v/(2*π))‖ = ‖𝓕 (deriv (deriv q)) (-v/(2*π))‖ := by
    rw [congrFun (Real.fourier_deriv hqdI (hqdC.differentiable (by simp)) hqddI) (-v/(2*π)),
      congrFun (Real.fourier_deriv hqI (hqC.differentiable (by simp)) hqdI) (-v/(2*π))]
    simp only [norm_smul,hcoeff,norm_mul,norm_neg,Complex.norm_real,
      Real.norm_eq_abs,Complex.norm_I,mul_one]
    rw [← mul_assoc,← pow_two,sq_abs]
  let B : ℝ := Real.exp (c*a)*(1+c)^2*(∫ x : ℝ, H x)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hbound (v : ℝ) : ‖profileLaplaceTransform f ((c:ℂ)+(v:ℂ)*I)‖ ≤ B*(1+v^2)⁻¹ := by
    rw [profileLaplaceTransform_eq_fourier]
    change ‖𝓕 q (-v/(2*π))‖ ≤ _
    apply (le_mul_inv_iff₀ (by positivity : 0 < 1+v^2)).mpr
    have hn : (1+v^2)*‖𝓕 q (-v/(2*π))‖ ≤ B := by
      calc
        _ = ‖𝓕 q (-v/(2*π))‖+‖𝓕 (deriv (deriv q)) (-v/(2*π))‖ := by rw [← hnorm]; ring
        _ ≤ (∫ x : ℝ, ‖q x‖)+(∫ x : ℝ, ‖deriv (deriv q) x‖) :=
          add_le_add (fourier_norm_le_L1 _ _) (fourier_norm_le_L1 _ _)
        _ = ∫ x : ℝ, ‖q x‖+‖deriv (deriv q) x‖ := (integral_add hqI.norm hqddI.norm).symm
        _ ≤ ∫ x : ℝ, Real.exp (c*a)*(1+c)^2*H x :=
          integral_mono (hqI.norm.add hqddI.norm) (hHI.const_mul _) hpoint
        _ = B := integral_const_mul _ _
    nlinarith
  have hi := integral_mono
    (profileLaplaceTransform_verticalIntegrable hf hfs c).norm
    (integrable_inv_one_add_sq.const_mul B) hbound
  rw [integral_const_mul] at hi
  exact hi.trans_eq (by dsimp [B]; ring)

theorem actualProfileTransformLine_L1_eventually_endpoint_bound
    {f : ℝ → ℂ} {a δ : ℝ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ Iic a) (hδ : 0 ≤ δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 < T → 1 ≤ Real.log T →
      (∫ y : ℝ, ‖actualProfileTransformLine f (Real.log T) δ y‖) ≤
        C*(Real.log T)^2*T^(δ*a) := by
  let D : ℝ := (∫ x : ℝ, ‖f x‖+2*‖deriv f x‖+‖deriv (deriv f) x‖)*
    (∫ v : ℝ, (1+v^2)⁻¹)
  have hD : 0 ≤ D := mul_nonneg
    (integral_nonneg (fun x => by positivity)) (integral_nonneg (fun x => by positivity))
  refine ⟨(1+δ)^2*D,by positivity,?_⟩
  intro T hT hlog
  have hL : 0 < Real.log T := Real.log_pos hT
  have hc : 0 ≤ Real.log T*δ := mul_nonneg hL.le hδ
  have hscale := Measure.integral_comp_mul_left
    (fun v : ℝ => ‖profileLaplaceTransform f ((Real.log T*δ:ℝ)+(v:ℂ)*I)‖)
    (Real.log T)
  have heq : (∫ y : ℝ, ‖actualProfileTransformLine f (Real.log T) δ y‖) =
      (Real.log T)⁻¹ * ∫ v : ℝ,
        ‖profileLaplaceTransform f ((Real.log T*δ:ℝ)+(v:ℂ)*I)‖ := by
    convert hscale using 1
    · apply integral_congr_ae
      filter_upwards [] with y
      unfold actualProfileTransformLine
      congr 2
      push_cast
      ring
    · simp only [abs_of_pos (inv_pos.mpr hL),smul_eq_mul]
  rw [heq]
  have hnorm0 : 0 ≤ ∫ v : ℝ,
      ‖profileLaplaceTransform f ((Real.log T*δ:ℝ)+(v:ℂ)*I)‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hinv : (Real.log T)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ hL).mpr hlog
  have hsquare : (1+Real.log T*δ)^2 ≤ (Real.log T)^2*(1+δ)^2 := by
    have hh : 1+Real.log T*δ ≤ Real.log T*(1+δ) := by nlinarith
    nlinarith [mul_nonneg hL.le hδ]
  have hexp : Real.exp ((Real.log T*δ)*a) = T^(δ*a) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hT)]
    congr 1
    ring
  calc
    _ ≤ ∫ v : ℝ, ‖profileLaplaceTransform f ((Real.log T*δ:ℝ)+(v:ℂ)*I)‖ := by nlinarith
    _ ≤ Real.exp ((Real.log T*δ)*a)*(1+Real.log T*δ)^2*D :=
      profileLaplaceTransform_L1_endpoint_bound hf hfs hsupp hc
    _ ≤ Real.exp ((Real.log T*δ)*a)*((Real.log T)^2*(1+δ)^2)*D := by
      gcongr
    _ = _ := by rw [hexp]; ring

theorem actualIntegratedProfileRemainder_uniform_eventually_power_decay
    {R δ κ a b : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ)
    (hab : a+b < 1) {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) (hfa : tsupport f ⊆ Iic a)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) (hgb : tsupport g ⊆ Iic b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      (∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖) →
      ∀ m : Fin 6, ∀ t : ℝ, T ≤ t →
        ‖actualIntegratedProfileRemainder T σ m f g (Real.log T) δ (t/(2*π))‖ ≤
          C*T^(-(δ*(1-a-b))/2) := by
  obtain ⟨B,hB,hbound⟩ := actualIntegratedProfileRemainder_uniform_log_bound hδ hδ1 hκ
  obtain ⟨F,hF,hFb⟩ := actualProfileTransformLine_L1_eventually_endpoint_bound hf hfs hfa hδ.le
  obtain ⟨G,hG,hGb⟩ := actualProfileTransformLine_L1_eventually_endpoint_bound hg hgs hgb hδ.le
  let ε : ℝ := δ*(1-a-b)
  have hε : 0 < ε := mul_pos hδ (by linarith)
  have hlogpow : ∀ᶠ T : ℝ in atTop, (Real.log T)^54 ≤ T^(ε/2) := by
    have hh := (isLittleO_log_rpow_rpow_atTop (54:ℝ) (show 0 < ε/2 by linarith)).bound
      (c := 1) (by norm_num)
    filter_upwards [hh,eventually_gt_atTop (1:ℝ)] with T hh hT
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (Real.log T)^54),
      abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) (ε/2)),one_mul] using hh
  let C : ℝ := (1/(2*π))^2*B*F*G*(2*π)^δ
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    rawMomentShifts_uniform_eventually_small hR (show 0 < δ/4 by linarith),hlogpow]
    with T hT hlog hraw hpow
  intro σ hσ hgap m t ht
  have hTp : 0 < T := zero_lt_one.trans hT
  have htp : 0 < t := hTp.trans_le ht
  have hp : 0 < 2*π := by positivity
  have hx : 0 < t/(2*π) := div_pos htp hp
  have hL : 0 < Real.log T := Real.log_pos hT
  have hscale : (t/(2*π))^(-δ) ≤ T^(-δ)*(2*π)^δ := by
    calc
      _ ≤ (T/(2*π))^(-δ) := Real.rpow_le_rpow_of_nonpos
        (div_pos hTp hp) (div_le_div_of_nonneg_right ht hp.le) (by linarith)
      _ = _ := by
        rw [Real.div_rpow hTp.le hp.le,Real.rpow_neg hp.le]
        simp only [div_eq_mul_inv,inv_inv]
  have hcombine : T^(-δ)*(T^(δ*a)*T^(δ*b)) = T^(-ε) := by
    rw [← Real.rpow_add hTp,← Real.rpow_add hTp]
    congr 1
    dsimp [ε]
    ring
  have hlast : T^(ε/2)*T^(-ε) = T^(-ε/2) := by
    rw [← Real.rpow_add hTp]
    congr 1
    ring
  calc
    _ ≤ (Real.log T/(2*π))^2*(B*(Real.log T)^48*(t/(2*π))^(-δ))*
        ((∫ y : ℝ, ‖actualProfileTransformLine f (Real.log T) δ y‖)*
          (∫ y : ℝ, ‖actualProfileTransformLine g (Real.log T) δ y‖)) :=
      hbound T hT hlog σ hgap (hraw σ hσ) m f g hf hfs hg hgs (Real.log T) hL _ hx
    _ ≤ (Real.log T/(2*π))^2*(B*(Real.log T)^48*(T^(-δ)*(2*π)^δ))*
        ((F*(Real.log T)^2*T^(δ*a))*(G*(Real.log T)^2*T^(δ*b))) := by
      gcongr
      · exact hFb T hT hlog
      · exact hGb T hT hlog
    _ = C*(Real.log T)^54*T^(-ε) := by
      dsimp [C]
      rw [div_pow]
      calc
        _ = ((1/(2*π))^2*B*F*G*(2*π)^δ)*(Real.log T)^54*
            (T^(-δ)*(T^(δ*a)*T^(δ*b))) := by ring
        _ = _ := by rw [hcombine]
    _ ≤ C*T^(ε/2)*T^(-ε) := by
      gcongr
    _ = C*T^(-ε/2) := by rw [mul_assoc,hlast]

theorem actualSmoothInteriorProfileRemainder_uniform_eventually_power_decay
    {R δ κ a b : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ)
    (hab : a+b < 1) {f g : ℝ → ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      (∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖) →
      ∀ m : Fin 6, ∀ t : ℝ, T ≤ t →
        ‖actualIntegratedProfileRemainder T σ m (fun x => (f x:ℂ))
          (fun x => (g x:ℂ)) (Real.log T) δ (t/(2*π))‖ ≤
          C*T^(-(δ*(1-a-b))/2) := by
  have hfa : tsupport (fun x => (f x:ℂ)) ⊆ Iic a := by
    have heq : Function.support (fun x => (f x:ℂ)) = Function.support f := by
      ext x
      change ((f x:ℂ) ≠ (0:ℂ)) ↔ f x ≠ (0:ℝ)
      exact not_congr Complex.ofReal_eq_zero
    intro x hx
    have hx' : x ∈ tsupport f := by simpa only [tsupport,heq] using hx
    exact (hf.2.2 hx').2.le
  have hgb : tsupport (fun x => (g x:ℂ)) ⊆ Iic b := by
    have heq : Function.support (fun x => (g x:ℂ)) = Function.support g := by
      ext x
      change ((g x:ℂ) ≠ (0:ℂ)) ↔ g x ≠ (0:ℝ)
      exact not_congr Complex.ofReal_eq_zero
    intro x hx
    have hx' : x ∈ tsupport g := by simpa only [tsupport,heq] using hx
    exact (hg.2.2 hx').2.le
  exact actualIntegratedProfileRemainder_uniform_eventually_power_decay
    hR hδ hδ1 hκ hab
    (hf.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hf.1) hfa
    (hg.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hg.1) hgb

private theorem actualSixPhase_norm_le {α : MomentShifts} {B : ℝ}
    (hB : 0 ≤ B) (hα : ∀ j : Fin 4, ‖α j‖ ≤ B) (m : Fin 6) :
    ‖bblrSixPhaseExponents α m‖ ≤ 4*B := by
  have h2 (i j : Fin 4) : ‖-α i-α j‖ ≤ 2*B := by
    have h := norm_sub_le (-α i) (α j)
    rw [norm_neg] at h
    linarith [hα i,hα j]
  have h3 : ‖-α 0-α 1-α 2‖ ≤ 3*B := by
    have h := norm_sub_le (-α 0-α 1) (α 2)
    linarith [h2 0 1,hα 2]
  have h4 : ‖-α 0-α 1-α 2-α 3‖ ≤ 4*B := by
    have h := norm_sub_le (-α 0-α 1-α 2) (α 3)
    linarith [hα 3]
  fin_cases m
  · change ‖(0:ℂ)‖ ≤ 4*B
    simpa only [norm_zero] using mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hB
  · simpa [bblrSixPhaseExponents] using h4
  · simpa [bblrSixPhaseExponents] using (h2 0 2).trans (by linarith : 2*B ≤ 4*B)
  · simpa [bblrSixPhaseExponents] using (h2 0 3).trans (by linarith : 2*B ≤ 4*B)
  · simpa [bblrSixPhaseExponents] using (h2 1 2).trans (by linarith : 2*B ≤ 4*B)
  · simpa [bblrSixPhaseExponents] using (h2 1 3).trans (by linarith : 2*B ≤ 4*B)

theorem actualSixPhase_uniform_eventually_norm_bound {R : ℝ} (hR : 0 ≤ R) :
    ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      ∀ m : Fin 6, ∀ t ∈ Icc T (2*T),
        ‖(t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)‖ ≤ Real.exp (8*R) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop (2*π),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Real.log 2))]
    with T hT hpT hlog
  intro σ hσ m t ht
  have hTp : 0 < T := zero_lt_one.trans hT
  have hL : 0 < Real.log T := Real.log_pos hT
  have hp : 0 < 2*π := by positivity
  have htp : 0 < t := hTp.trans_le ht.1
  have hx : 0 < t/(2*π) := div_pos htp hp
  have hx1 : 1 ≤ t/(2*π) := (le_div_iff₀ hp).mpr
    (by simpa only [one_mul] using hpT.trans ht.1)
  have hlogx0 : 0 ≤ Real.log (t/(2*π)) := Real.log_nonneg hx1
  have hxle : t/(2*π) ≤ 2*T := by
    apply (div_le_iff₀ hp).mpr
    have hp1 : 1 ≤ 2*π := by nlinarith [Real.pi_gt_three]
    nlinarith [ht.2]
  have hlogx : Real.log (t/(2*π)) ≤ 2*Real.log T := by
    have h := Real.log_le_log hx hxle
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hTp.ne'] at h
    linarith
  have hraw (j : Fin 4) : ‖rawMomentShifts T σ j‖ ≤ R/Real.log T := by
    rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_of_nonneg hL.le]
    exact div_le_div_of_nonneg_right (hσ j) hL.le
  have he := (Complex.re_le_norm (bblrSixPhaseExponents (rawMomentShifts T σ) m)).trans
    (actualSixPhase_norm_le (div_nonneg hR hL.le) hraw m)
  have hcast : (t/(2*π):ℂ) = ((t/(2*π):ℝ):ℂ) := by push_cast; rfl
  rw [hcast,Complex.norm_cpow_eq_rpow_re_of_pos hx,Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ Real.log (t/(2*π))*(4*(R/Real.log T)) :=
      mul_le_mul_of_nonneg_left he hlogx0
    _ ≤ (2*Real.log T)*(4*(R/Real.log T)) :=
      mul_le_mul_of_nonneg_right hlogx (by positivity)
    _ = _ := by field_simp; ring

private theorem actualPureLeft_continuous (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    {δ : ℝ} (hδ : 0 < δ)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4) :
    Continuous (fun s : ℝ => purePolarZetaProduct T σ m ((-δ/2:ℝ)+(s:ℂ)*I)) := by
  unfold purePolarZetaProduct
  apply continuous_finsetProd
  intro ij _
  apply continuous_iff_continuousAt.mpr
  intro s
  have hre := (Complex.abs_re_le_norm (purePolarRoot T σ (m,ij))).trans
    (purePolarRoot_norm_le_of_rawShifts hα (m,ij))
  have hne : 1+2*(((-δ/2:ℝ)+(s:ℂ)*I)-purePolarRoot T σ (m,ij)) ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith [(abs_le.mp hre).1]
  exact ContinuousAt.comp (f := fun s : ℝ =>
    1+2*(((-δ/2:ℝ)+(s:ℂ)*I)-purePolarRoot T σ (m,ij))) (g := riemannZeta)
    (differentiableAt_riemannZeta hne).continuousAt (by fun_prop)

theorem actualIntegratedProfileRemainder_clipped_stronglyMeasurable
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {L δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) :
    StronglyMeasurable (fun t : ℝ => actualIntegratedProfileRemainder T σ m f g L δ
      ((max t 1)/(2*π))) := by
  let F : (ℝ × (ℝ × ℝ)) × ℝ → ℂ := fun w =>
    actualProfileTransformProduct f g L δ w.1.2*
      (polarMellinArithmeticKernel T σ m ((δ:ℂ)+(w.1.2.1:ℂ)*I)
        ((δ:ℂ)+(w.1.2.2:ℂ)*I) ((-δ/2:ℝ)+(w.2:ℂ)*I)/
          ((-δ/2:ℝ)+(w.2:ℂ)*I)*(((max w.1.1 1)/(2*π):ℝ):ℂ)^
            (2*((-δ/2:ℝ)+(w.2:ℂ)*I)))
  have hshift (j : Fin 4) : ‖bblrSixShifts (rawMomentShifts T σ) m j‖ ≤ δ/4 :=
    bblrSixShifts_norm_le _ hα m j
  have hP : Continuous (fun w : (ℝ × (ℝ × ℝ)) × ℝ =>
      actualProfileTransformProduct f g L δ w.1.2) := by
    unfold actualProfileTransformProduct actualProfileTransformLine
    exact ((profileLaplaceTransform_differentiable hf hfs.continuous).continuous.comp
      (by fun_prop)).mul
        ((profileLaplaceTransform_differentiable hg hgs.continuous).continuous.comp (by fun_prop))
  have hA := (entangled_profile_continuous hδ hδ1 hshift (le_refl (-δ/2))).comp
    (show Continuous (fun w : (ℝ × (ℝ × ℝ)) × ℝ => (w.1.2,w.2)) by fun_prop)
  have hG := (polarPoleKiller_differentiable T σ).continuous.comp
    (show Continuous (fun w : (ℝ × (ℝ × ℝ)) × ℝ => ((-δ/2:ℝ)+(w.2:ℂ)*I)) by fun_prop)
  have hZ := (actualPureLeft_continuous T σ m hδ hα).comp
    (show Continuous (fun w : (ℝ × (ℝ × ℝ)) × ℝ => w.2) by fun_prop)
  have hz : Continuous (fun w : (ℝ × (ℝ × ℝ)) × ℝ => ((-δ/2:ℝ)+(w.2:ℂ)*I : ℂ)) := by fun_prop
  have hzne (w : (ℝ × (ℝ × ℝ)) × ℝ) : ((-δ/2:ℝ)+(w.2:ℂ)*I : ℂ) ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
    linarith
  have hpow : Continuous (fun w : (ℝ × (ℝ × ℝ)) × ℝ =>
      (((max w.1.1 1)/(2*π):ℝ):ℂ)^(2*((-δ/2:ℝ)+(w.2:ℂ)*I))) :=
    Continuous.cpow (by fun_prop) (by fun_prop) (fun w => ofReal_mem_slitPlane.mpr
      (div_pos ((by norm_num : (0:ℝ) < 1).trans_le (le_max_right _ _)) (by positivity)))
  have hF : Continuous F := by
    convert hP.mul (((hA.mul (hG.mul hZ)).div hz hzne).mul hpow) using 1
    funext w
    rfl
  have hi := (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).integral_prod_right'
    (ν := volume.prod volume)
  have hc := hi.const_mul (((L:ℂ)/(2*π))^2*(1/(2*π):ℂ))
  convert hc using 1
  funext t
  unfold actualIntegratedProfileRemainder polarMellinRemainderIntegral verticalIntegral
  dsimp only [F]
  simp_rw [integral_const_mul]
  rw [mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

def actualSixProfileRemainderMoment (T : ℝ) (σ : MomentShifts)
    (f g : ℝ → ℂ) (Φ : ℝ → ℝ) (δ : ℝ) : ℂ :=
  ∫ t : ℝ, ∑ m : Fin 6, (Φ (t/T):ℂ)*
    (t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)*
    actualIntegratedProfileRemainder T σ m f g (Real.log T) δ (t/(2*π))

theorem actualSixProfileRemainderMoment_uniform_eventually_integrable_power_bound
    {R δ κ a b : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ)
    (hab : a+b < 1) {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) (hfa : tsupport f ⊆ Iic a)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) (hgb : tsupport g ⊆ Iic b)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      (∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖) →
      (Integrable (fun t : ℝ => ∑ m : Fin 6, (Φ (t/T):ℂ)*
        (t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)*
        actualIntegratedProfileRemainder T σ m f g (Real.log T) δ (t/(2*π)))) ∧
      ‖actualSixProfileRemainderMoment T σ f g Φ δ‖ ≤ C*T^(1-(δ*(1-a-b))/2) := by
  obtain ⟨B,hB,hbound⟩ := actualIntegratedProfileRemainder_uniform_eventually_power_decay
    hR hδ hδ1 hκ hab hf hfs hfa hg hgs hgb
  have hΦK : HasCompactSupport Φ :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hΦ.2
  have hΦI : Integrable Φ := hΦ.1.continuous.integrable_of_hasCompactSupport hΦK
  let A : ℝ := 6*Real.exp (8*R)*B
  let J : ℝ := ∫ x : ℝ, ‖Φ x‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hJ : 0 ≤ J := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨A*J,mul_nonneg hA hJ,?_⟩
  filter_upwards [hbound,actualSixPhase_uniform_eventually_norm_bound hR,
    eventually_gt_atTop (1:ℝ),
    rawMomentShifts_uniform_eventually_small hR (show 0 < δ/4 by linarith)]
    with T hbound hphase hT hraw
  intro σ hσ hgap
  have hTp : 0 < T := zero_lt_one.trans hT
  have hα := hraw σ hσ
  have hsupport (t : ℝ) (ht : Φ (t/T) ≠ 0) : t ∈ Icc T (2*T) := by
    have hh := hΦ.2 (subset_tsupport Φ ht)
    constructor
    · exact (by simpa only [one_mul] using (le_div_iff₀ hTp).mp hh.1)
    · exact (div_le_iff₀ hTp).mp hh.2
  let E : ℝ → ℂ := fun t => ∑ m : Fin 6, (Φ (t/T):ℂ)*
    (t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)*
    actualIntegratedProfileRemainder T σ m f g (Real.log T) δ (t/(2*π))
  have hEm : StronglyMeasurable E := by
    have hcl : StronglyMeasurable (fun t : ℝ => ∑ m : Fin 6, (Φ (t/T):ℂ)*
        (((max t 1)/(2*π):ℝ):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)*
        actualIntegratedProfileRemainder T σ m f g (Real.log T) δ ((max t 1)/(2*π))) := by
      suffices hs : StronglyMeasurable (∑ m : Fin 6, fun t : ℝ => (Φ (t/T):ℂ)*
          (((max t 1)/(2*π):ℝ):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)*
          actualIntegratedProfileRemainder T σ m f g (Real.log T) δ ((max t 1)/(2*π))) by
        convert hs using 1
        funext t
        simp only [Finset.sum_apply]
      apply Finset.stronglyMeasurable_sum
      intro m _
      have hw : Continuous (fun t : ℝ => (Φ (t/T):ℂ)*
          (((max t 1)/(2*π):ℝ):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)) :=
        (Complex.continuous_ofReal.comp (hΦ.1.continuous.comp (by fun_prop))).mul
          (Continuous.cpow (by fun_prop) continuous_const (fun t => ofReal_mem_slitPlane.mpr
            (div_pos ((by norm_num : (0:ℝ) < 1).trans_le (le_max_right _ _)) (by positivity))))
      exact hw.stronglyMeasurable.mul
        (actualIntegratedProfileRemainder_clipped_stronglyMeasurable T σ m
          hδ hδ1 hα hf hfs hg hgs)
    convert hcl using 1
    funext t
    apply Finset.sum_congr rfl
    intro m _
    by_cases ht : Φ (t/T)=0
    · simp [ht]
    · have ht1 : 1 ≤ t := hT.le.trans (hsupport t ht).1
      rw [max_eq_left ht1]
      push_cast
      rfl
  have hEnorm (t : ℝ) : ‖E t‖ ≤ (A*T^(-(δ*(1-a-b))/2))*‖Φ (t/T)‖ := by
    by_cases ht : Φ (t/T)=0
    · simp [E,ht]
    · have htS := hsupport t ht
      calc
        _ ≤ ∑ m : Fin 6, ‖(Φ (t/T):ℂ)*
            (t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)*
            actualIntegratedProfileRemainder T σ m f g (Real.log T) δ (t/(2*π))‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _m : Fin 6, ‖Φ (t/T)‖*Real.exp (8*R)*(B*T^(-(δ*(1-a-b))/2)) := by
          apply Finset.sum_le_sum
          intro m _
          rw [norm_mul,norm_mul,Complex.norm_real]
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hphase σ hσ m t htS) (norm_nonneg _))
            (hbound σ hσ hgap m t htS.1) (norm_nonneg _) (by positivity)
        _ = _ := by
          simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
          dsimp [A]
          ring
  have hdom : Integrable (fun t : ℝ => (A*T^(-(δ*(1-a-b))/2))*‖Φ (t/T)‖) :=
    (hΦI.norm.comp_div hTp.ne').const_mul _
  have hEI : Integrable E := hdom.mono' hEm.aestronglyMeasurable (Eventually.of_forall hEnorm)
  refine ⟨hEI,?_⟩
  have hN := norm_integral_le_of_norm_le hdom (Eventually.of_forall hEnorm)
  rw [integral_const_mul] at hN
  have hscale := Measure.integral_comp_div (fun x : ℝ => ‖Φ x‖) T
  rw [abs_of_pos hTp,smul_eq_mul] at hscale
  rw [hscale] at hN
  have hpow : T*T^(-(δ*(1-a-b))/2) = T^(1-(δ*(1-a-b))/2) := by
    nth_rw 1 [← Real.rpow_one T]
    rw [← Real.rpow_add hTp]
    congr 1
    ring
  change ‖∫ t : ℝ, E t‖ ≤ _
  exact hN.trans_eq (by change (A*T^(-(δ*(1-a-b))/2))*(T*J) = _; rw [← hpow]; ring)

theorem actualSixProfileRemainderMoment_uniform_eventually_negligible
    {R δ κ a b : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ)
    (hab : a+b < 1) {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f) (hfa : tsupport f ⊆ Iic a)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g) (hgb : tsupport g ⊆ Iic b)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      (∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖) →
        ‖actualSixProfileRemainderMoment T σ f g Φ δ‖ ≤ ε*T := by
  obtain ⟨C,hC,hbound⟩ := actualSixProfileRemainderMoment_uniform_eventually_integrable_power_bound
    hR hδ hδ1 hκ hab hf hfs hfa hg hgs hgb Φ hΦ
  have hεp : 0 < δ*(1-a-b)/2 := div_pos (mul_pos hδ (by linarith)) (by norm_num)
  have hp := (rpow_isLittleO_id_of_lt_one (show 1-(δ*(1-a-b))/2 < 1 by linarith)).const_mul_left C
  intro ε hε
  filter_upwards [hbound,hp.def hε,eventually_gt_atTop (0:ℝ)] with T hb hp hT
  intro σ hσ hgap
  apply (hb σ hσ hgap).2.trans
  simpa only [Real.norm_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hT.le _)),
    Real.norm_of_nonneg hT.le] using hp

private theorem actualRealProfile_tsupport_eq (f : ℝ → ℝ) :
    tsupport (fun x => (f x:ℂ)) = tsupport f := by
  unfold tsupport
  congr 1
  ext x
  change ((f x:ℂ) ≠ (0:ℂ)) ↔ f x ≠ (0:ℝ)
  exact not_congr Complex.ofReal_eq_zero

theorem actualSmoothSixProfileRemainderMoment_uniform_eventually_integrable_power_bound
    {R δ κ a b : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ)
    (hab : a+b < 1) {f g : ℝ → ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      (∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖) →
      (Integrable (fun t : ℝ => ∑ m : Fin 6, (Φ (t/T):ℂ)*
        (t/(2*π):ℂ)^(bblrSixPhaseExponents (rawMomentShifts T σ) m)*
        actualIntegratedProfileRemainder T σ m (fun x => (f x:ℂ)) (fun x => (g x:ℂ))
          (Real.log T) δ (t/(2*π)))) ∧
      ‖actualSixProfileRemainderMoment T σ (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ δ‖ ≤
        C*T^(1-(δ*(1-a-b))/2) := by
  apply actualSixProfileRemainderMoment_uniform_eventually_integrable_power_bound
    hR hδ hδ1 hκ hab
    (hf.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hf.1)
    (by change tsupport (fun x => (f x:ℂ)) ⊆ Iic a; rw [actualRealProfile_tsupport_eq]; exact fun x hx => (hf.2.2 hx).2.le)
    (hg.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hg.1)
    (by change tsupport (fun x => (g x:ℂ)) ⊆ Iic b; rw [actualRealProfile_tsupport_eq]; exact fun x hx => (hg.2.2 hx).2.le) Φ hΦ

theorem actualSmoothSixProfileRemainderMoment_uniform_eventually_negligible
    {R δ κ a b : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ) (hδ1 : δ < 1/4) (hκ : 0 < κ)
    (hab : a+b < 1) {f g : ℝ → ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
      ∀ σ : MomentShifts, (∀ j : Fin 4, ‖σ j‖ ≤ R) →
      (∀ k : PurePolarIndex, κ ≤ ‖normalizedPurePolarRoot σ k‖) →
        ‖actualSixProfileRemainderMoment T σ (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ δ‖ ≤ ε*T := by
  exact actualSixProfileRemainderMoment_uniform_eventually_negligible hR hδ hδ1 hκ hab
    (hf.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hf.1)
    (by change tsupport (fun x => (f x:ℂ)) ⊆ Iic a; rw [actualRealProfile_tsupport_eq]; exact fun x hx => (hf.2.2 hx).2.le)
    (hg.2.1.comp_left (show Complex.ofReal 0=0 from rfl))
    (Complex.ofRealCLM.contDiff.comp hg.1)
    (by change tsupport (fun x => (g x:ℂ)) ⊆ Iic b; rw [actualRealProfile_tsupport_eq]; exact fun x hx => (hg.2.2 hx).2.le) Φ hΦ

end
end SixthMoment
