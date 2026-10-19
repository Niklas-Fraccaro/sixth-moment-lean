import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.FrontFubini
import Sechstmoment.Numerator.U.ZeroModes.Ratio.PhysicalResidualGrowth

/-! Exact initial physical GCD front = literal double residue + the
three actual residual contours, after genuine full positive-x Fubini. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeGCDEtaMainX (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (g a b : ℕ) (A B : ℕ→ℂ) (s : ℂ) : ℂ :=
  ∫x : ℝ in Ioi 0,(x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
    (a03ZeroModeRatioPhysicalPrefactor α g a b A B x s*a03ZeroModeRatioArithmeticNumerator α a b 0 0 s)

theorem a03ZeroModeGCDEtaResidualX_integrable
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T η : ℝ} (hT : 0<T) (hη : 0<η) (hη1 : η≤1/16)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤η/32)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {s : ℂ} (hs : s.re=1+η/4) :
    IntegrableOn (fun x : ℝ => (x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
      a03ZeroModeRatioPhysicalResidual (η/4) α g a b A B x s) (Ioi 0) := by
  have hε : 0<η/4 := by positivity
  have hε1 : η/4<1/8 := by linarith
  have hα' : ∀ j : Fin 4,‖α j‖≤(η/4)/8 := by
    simpa only [div_div,show (4:ℝ)*8=32 by norm_num] using hα
  obtain ⟨Cr,hCr,hRes⟩ := a03ZeroModeRatioPhysicalResidual_growth_bound hε hε1 hε α hα' hρ
  have hcs : s.re∈Icc (1/8:ℝ) (15/8) := by rw [hs]; constructor <;> linarith
  obtain ⟨Ca,hCa,hArch⟩ := a03ZeroModeGCDArchKernel_full_height_envelope hΦ hSupp hcs 0
  have hCG := polarGaussianConstant_nonneg T σ 1
  let Q : ℝ := Ca*(1+polarGaussianConstant T σ 1)*Cr*T^(-s.re)
  have hQ : 0≤Q := by dsimp [Q]; positivity
  let J : Fin 3→ℝ→ℝ := fun j => a03ZeroModeRatioPhysicalXMajorant T (η/4) (η/4) s.re α g a b A B s j
  have hJ (j : Fin 3) : IntegrableOn (J j) (Ioi 0) := by
    simpa only [J,hs] using
      (a03ZeroModeRatioPhysicalXMajorant_integrable_and_mass hT hη hη1 α hα hg ha hb A B s j).1
  have hSum : IntegrableOn (fun x => ∑ j : Fin 3,J j x) (Ioi 0) := integrable_finsetSum _ (fun j _ => hJ j)
  have hMeas : AEStronglyMeasurable (fun x : ℝ => (x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
      a03ZeroModeRatioPhysicalResidual (η/4) α g a b A B x s) (volume.restrict (Ioi 0)) :=
    (((Complex.measurable_ofReal.inv).aestronglyMeasurable.restrict).mul
      (a03ZeroModeGCDArchKernel_aestronglyMeasurable hΦ hSupp hT σ hg ha hb (by linarith))).mul
    (a03ZeroModeRatioPhysicalResidual_measurable_comp (η/4) α g ha.ne' hb.ne' A B measurable_id measurable_const).aestronglyMeasurable.restrict
  apply (hSum.const_mul Q).mono' hMeas
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hEnv := a03ZeroModeRatioXEnvelope_nonneg (a03ZeroModeRatioPhysicalScale T g a b) x
  have hxT : 0≤x/T := (div_pos hx hT).le
  have hArchMajorant : 0≤Ca*(1+polarGaussianConstant T σ 1)*(x/T)^s.re*
      a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x := by
    exact mul_nonneg (by positivity) hEnv
  have hYeq : a03ZeroModeRatioPhysicalScale T g a b=T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)) := by
    rw [a03ZeroModeRatioPhysicalScale_eq,Nat.cast_mul]
  have hA := hArch T hT σ g a b hg ha hb x hx s rfl
  simp only [pow_zero,one_mul] at hA
  rw [←hYeq] at hA
  have hR := hRes g a b hg ha hb A B x hx s (by linarith : 1+η/4≤s.re)
  rw [norm_mul,norm_mul]
  calc
    _≤‖(x:ℂ)⁻¹‖*(Ca*(1+polarGaussianConstant T σ 1)*(x/T)^s.re*
      a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x)*
      (Cr*‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖*(a:ℝ)^(η/4)*(b:ℝ)^(η/4)*
        ((x/(g*a:ℕ))^(a03ZeroModeRatioPrimaryLine (η/4))*(x/(g*b:ℕ))^(a03ZeroModeRatioPrimaryLine (η/4))+
         (x/(g*b:ℕ))^(a03ZeroModeRatioSecondaryLine (η/4))+(x/(g*a:ℕ))^(a03ZeroModeRatioSecondaryLine (η/4)))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hA (norm_nonneg _)) hR (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) hArchMajorant)
    _=Q*(∑ j : Fin 3,J j x) := by
      dsimp only [Q,J]
      rw [a03ZeroModeRatioPhysicalXMajorant_sum]
      have hp := a03ZeroModeGCDEtaResidual_density_power hT hx (cs := s.re)
      calc
        _=(Ca*(1+polarGaussianConstant T σ 1)*Cr)*(‖(x:ℂ)⁻¹‖*(x/T)^s.re)*
          (‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖*(a:ℝ)^(η/4)*(b:ℝ)^(η/4)*
            ((x/(g*a:ℕ))^(a03ZeroModeRatioPrimaryLine (η/4))*(x/(g*b:ℕ))^(a03ZeroModeRatioPrimaryLine (η/4))+
             (x/(g*b:ℕ))^(a03ZeroModeRatioSecondaryLine (η/4))+(x/(g*a:ℕ))^(a03ZeroModeRatioSecondaryLine (η/4)))*
              a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x) := by ring
        _=_ := by rw [hp]; ring

theorem a03ZeroModeGCDEtaFrontBlock_initial_reconstruction
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T η : ℝ} (hT : 0<T) (hη : 0<η) (hη1 : η≤1/16)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤η/32)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {s : ℂ} (hs : s.re=1+η/4) :
    IntegrableOn (fun x : ℝ => (x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
      (a03ZeroModeRatioPhysicalPrefactor α g a b A B x s*a03ZeroModeRatioArithmeticNumerator α a b 0 0 s)) (Ioi 0) ∧
    a03ZeroModeRatioDoubleIntegral (η/4) (η/4) (fun u v => a03ZeroModeGCDEtaFrontBlock Φ T σ α g a b A B u v s)=
      a03ZeroModeGCDEtaMainX Φ T σ α g a b A B s+a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B s := by
  have hε : 0<η/4 := by positivity
  have hε1 : η/4<1/8 := by linarith
  have hα' : ∀ j : Fin 4,‖α j‖≤(η/4)/8 := by
    simpa only [div_div,show (4:ℝ)*8=32 by norm_num] using hα
  let F : ℝ×(ℝ×ℝ)→ℂ := fun p => a03ZeroModeGCDInitialDensity Φ T σ α g a b A B p.1
    (((η/4:ℝ):ℂ)+(p.2.1:ℂ)*I) (((η/4:ℝ):ℂ)+(p.2.2:ℂ)*I) s
  have hJoint : Integrable F ((volume.restrict (Ioi 0)).prod (volume.prod volume)) :=
    a03ZeroModeGCDInitialDensity_joint_integrable hΦ hSupp hT hε hε1 σ α hα' hρ hg ha hb A B hs
  let H : ℝ→ℂ := fun x => (x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
    a03ZeroModeRatioDoubleIntegral (η/4) (η/4) (fun u v => a03ZeroModeRatioPhysicalKernel α g a b A B x u v s)
  let R : ℝ→ℂ := fun x => (x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
    a03ZeroModeRatioPhysicalResidual (η/4) α g a b A B x s
  let M : ℝ→ℂ := fun x => (x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
    (a03ZeroModeRatioPhysicalPrefactor α g a b A B x s*a03ZeroModeRatioArithmeticNumerator α a b 0 0 s)
  have hH : IntegrableOn H (Ioi 0) := by
    apply (hJoint.integral_prod_left.const_mul ((1/(2*Real.pi):ℂ)^2)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi,hJoint.prod_right_ae] with x hx hi
    change (1/(2*Real.pi):ℂ)^2*(∫p : ℝ×ℝ,
      a03ZeroModeGCDInitialDensity Φ T σ α g a b A B x
        (((η/4:ℝ):ℂ)+(p.1:ℂ)*I) (((η/4:ℝ):ℂ)+(p.2:ℂ)*I) s ∂(volume.prod volume))=H x
    rw [←a03ZeroModeRatioDoubleIntegral_eq_product (η/4) (η/4)
      (fun u v => a03ZeroModeGCDInitialDensity Φ T σ α g a b A B x u v s) hi]
    unfold a03ZeroModeGCDInitialDensity H
    rw [a03ZeroModeRatioDoubleIntegral_const_mul]
  have hR : IntegrableOn R (Ioi 0) :=
    a03ZeroModeGCDEtaResidualX_integrable hΦ hSupp hT hη hη1 σ α hα hρ hg ha hb A B hs
  have hPoint (x : ℝ) (hx : 0<x) : H x=M x+R x := by
    dsimp only [H,M,R]
    rw [a03ZeroModeRatioPhysicalKernel_eq_main_add_residual hε hε1 hε α hα' hρ hg ha hb A B hx (by linarith)]
    ring
  have hM : IntegrableOn M (Ioi 0) := (hH.sub hR).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change H x-R x=M x
    rw [hPoint x hx,add_sub_cancel_right])
  refine ⟨hM,?_⟩
  rw [a03ZeroModeGCDEtaFrontBlock_initial_fubini hΦ hSupp hT hε hε1 σ α hα' hρ hg ha hb A B hs]
  change (∫x in Ioi (0:ℝ),H x)=(∫x in Ioi (0:ℝ),M x)+(∫x in Ioi (0:ℝ),R x)
  rw [←integral_add hM hR]
  apply setIntegral_congr_fun measurableSet_Ioi
  exact hPoint

/-- The remaining outer contour is additive once its two actual absolute
convergence facts have been established.  In particular the main contour's
integrability is a conclusion, obtained from front minus residual. -/
theorem a03ZeroModeGCDEtaFrontBlock_outer_reconstruction
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T η : ℝ} (hT : 0<T) (hη : 0<η) (hη1 : η≤1/16)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤η/32)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    (hFront : Integrable (fun y : ℝ => a03ZeroModeRatioDoubleIntegral (η/4) (η/4)
      (fun u v => a03ZeroModeGCDEtaFrontBlock Φ T σ α g a b A B u v
        (((1+η/4:ℝ):ℂ)+(y:ℂ)*I))))
    (hResidual : Integrable (fun y : ℝ => a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B
        (((1+η/4:ℝ):ℂ)+(y:ℂ)*I))) :
    Integrable (fun y : ℝ => a03ZeroModeGCDEtaMainX Φ T σ α g a b A B
      (((1+η/4:ℝ):ℂ)+(y:ℂ)*I)) ∧
    verticalIntegral (1+η/4) (fun s => a03ZeroModeRatioDoubleIntegral (η/4) (η/4)
      (fun u v => a03ZeroModeGCDEtaFrontBlock Φ T σ α g a b A B u v s))=
      verticalIntegral (1+η/4) (a03ZeroModeGCDEtaMainX Φ T σ α g a b A B)+
        verticalIntegral (1+η/4) (a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B) := by
  have he (y : ℝ) :
      a03ZeroModeRatioDoubleIntegral (η/4) (η/4) (fun u v =>
        a03ZeroModeGCDEtaFrontBlock Φ T σ α g a b A B u v (((1+η/4:ℝ):ℂ)+(y:ℂ)*I))=
      a03ZeroModeGCDEtaMainX Φ T σ α g a b A B (((1+η/4:ℝ):ℂ)+(y:ℂ)*I)+
        a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B (((1+η/4:ℝ):ℂ)+(y:ℂ)*I) :=
    (a03ZeroModeGCDEtaFrontBlock_initial_reconstruction hΦ hSupp hT hη hη1
      σ α hα hρ hg ha hb A B (by simp)).2
  have hMain : Integrable (fun y : ℝ => a03ZeroModeGCDEtaMainX Φ T σ α g a b A B
      (((1+η/4:ℝ):ℂ)+(y:ℂ)*I)) := (hFront.sub hResidual).congr (ae_of_all _ (fun y => by
    dsimp only [Pi.sub_apply]
    rw [he y,add_sub_cancel_right]))
  refine ⟨hMain,?_⟩
  unfold verticalIntegral
  simp_rw [he]
  rw [integral_add hMain hResidual]
  ring

end
end Sechstmoment.Source
