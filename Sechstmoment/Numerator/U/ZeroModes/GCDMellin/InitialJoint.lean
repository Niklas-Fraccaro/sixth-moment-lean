import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.ResidualBudget
import Sechstmoment.Numerator.U.ZeroModes.Ratio.PhysicalMeasurability

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeGCDInitialDensity (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (g a b : ℕ) (A B : ℕ→ℂ) (x : ℝ) (u v s : ℂ) : ℂ :=
  (x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
    a03ZeroModeRatioPhysicalKernel α g a b A B x u v s

theorem a03ZeroModeGCDInitialDensity_joint_integrable
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {s : ℂ} (hs : s.re=1+ε) :
    Integrable (fun p : ℝ×(ℝ×ℝ) => a03ZeroModeGCDInitialDensity Φ T σ α g a b A B p.1
      ((ε:ℂ)+(p.2.1:ℂ)*I) ((ε:ℂ)+(p.2.2:ℂ)*I) s)
      ((volume.restrict (Ioi 0)).prod (volume.prod volume)) := by
  have hq : a03ZeroModeRatioSecondaryLine ε≤ε := by unfold a03ZeroModeRatioSecondaryLine; linarith
  have h2q : a03ZeroModeRatioSecondaryLine ε≤ε+ε := by unfold a03ZeroModeRatioSecondaryLine; linarith
  have hcs : s.re∈Icc (1/8:ℝ) (15/8) := by rw [hs]; constructor <;> linarith
  have hB := abs_le.mp ((Complex.abs_re_le_norm (α 1)).trans (hα 1))
  have hD := abs_le.mp ((Complex.abs_re_le_norm (α 3)).trans (hα 3))
  let r : ℝ := s.re+2*ε-(α 1).re-(α 3).re
  have hr : 0<r := by dsimp [r]; rw [hs]; linarith
  have hr2 : r<2 := by dsimp [r]; rw [hs]; linarith
  let Y := a03ZeroModeRatioPhysicalScale T g a b
  have hY : 0<Y := a03ZeroModeRatioPhysicalScale_pos hT hg ha hb
  let Q : ℝ := ‖A (g*a)‖*‖B (g*b)‖*(g:ℝ)^(-1+(α 1).re+(α 3).re-s.re-2*ε)*
    (a:ℝ)^(-1+(α 1).re-ε)*(b:ℝ)^(-1+(α 3).re-ε)
  let P : ℝ→ℝ := fun x => x^(s.re-1)*‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖*
    ((x/(g*a:ℕ))^ε*(x/(g*b:ℕ))^ε)*a03ZeroModeRatioXEnvelope Y x
  have hP : IntegrableOn P (Ioi 0) := by
    have hbase : IntegrableOn (fun x : ℝ => Q*(x^(r-1)*a03ZeroModeRatioXEnvelope Y x)) (Ioi 0) :=
      (a03ZeroModeRatioXEnvelope_weight_integrable hY hr hr2).const_mul Q
    apply hbase.congr_fun _ measurableSet_Ioi
    intro x hx
    have hn := a03ZeroModeRatioPhysicalPrefactor_gain_norm α hg ha hb A B hx s 0 ε ε (2*ε) (by ring)
    simp only [Real.rpow_zero,mul_one,add_zero] at hn
    change ‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖*
      ((x/(g*a:ℕ))^ε*(x/(g*b:ℕ))^ε)=Q*x^(2*ε-(α 1).re-(α 3).re) at hn
    have hpow : x^(s.re-1)*x^(2*ε-(α 1).re-(α 3).re)=x^(r-1) := by
      rw [←Real.rpow_add hx]
      congr 1
      dsimp [r]
      ring
    change Q*(x^(r-1)*a03ZeroModeRatioXEnvelope Y x)=P x
    calc
      _=x^(s.re-1)*(Q*x^(2*ε-(α 1).re-(α 3).re))*a03ZeroModeRatioXEnvelope Y x := by
        rw [←hpow]
        ring
      _=P x := by dsimp only [P]; rw [←hn]; ring
  let G : ℝ→ℝ := fun y => (1+|y|)^4*Real.exp (Real.pi*|y|-y^2)
  have hG : Integrable G := Sechstmoment.gaussianPolynomialExponential_integrable 4 Real.pi
  obtain ⟨C,hC,hKernel⟩ := a03ZeroModeRatioArithmeticKernel_boundary_majorant hε hε α hα hρ
    ha.ne' hb.ne' (by linarith : 1+ε≤s.re) hq hq h2q
    (by rw [abs_of_pos hε]; linarith) (by rw [abs_of_pos hε]; linarith)
    (by rw [abs_of_pos hε]) (by rw [abs_of_pos hε])
  obtain ⟨D,hDd,hArch⟩ := a03ZeroModeGCDArchKernel_full_height_envelope hΦ hSupp hcs 0
  have hCG := polarGaussianConstant_nonneg T σ 1
  let C0 : ℝ := D*(1+polarGaussianConstant T σ 1)*C*T^(-s.re)
  have hC0 : 0≤C0 := by dsimp [C0]; positivity
  have hmajorant : Integrable (fun p : ℝ×(ℝ×ℝ) => C0*P p.1*G p.2.1*G p.2.2)
      ((volume.restrict (Ioi 0)).prod (volume.prod volume)) := by
    convert (hP.mul_prod (hG.mul_prod hG)).const_mul C0 using 1
    funext p
    ring
  have hX : Measurable (fun p : ℝ×(ℝ×ℝ) => p.1) := measurable_fst
  have hArchM : Measurable (fun p : ℝ×(ℝ×ℝ) => a03ZeroModeGCDArchTimeKernel Φ T σ g a b p.1 s) :=
    a03ZeroModeGCDArchTimeKernel_measurable_comp Φ hΦ.continuous.measurable T σ g a b hX measurable_const
  have hPhysM := a03ZeroModeRatioPhysicalKernel_measurable_boundary hε α hα ha.ne' hb.ne'
    (by linarith : 1≤s.re) hq hq h2q hε.ne' hε.ne' g A B
  have hTimeM : Measurable (fun p : ℝ×(ℝ×ℝ) => (p.1:ℂ)⁻¹*
      a03ZeroModeGCDArchTimeKernel Φ T σ g a b p.1 s*
        a03ZeroModeRatioPhysicalKernel α g a b A B p.1
          ((ε:ℂ)+(p.2.1:ℂ)*I) ((ε:ℂ)+(p.2.2:ℂ)*I) s) :=
    (((Complex.measurable_ofReal.comp hX).inv).mul hArchM).mul hPhysM
  have hPos : ∀ᵐ p : ℝ×(ℝ×ℝ) ∂((volume.restrict (Ioi 0)).prod (volume.prod volume)),0<p.1 :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually (ae_restrict_mem measurableSet_Ioi)
  have hMeas : AEStronglyMeasurable (fun p : ℝ×(ℝ×ℝ) => a03ZeroModeGCDInitialDensity Φ T σ α g a b A B p.1
      ((ε:ℂ)+(p.2.1:ℂ)*I) ((ε:ℂ)+(p.2.2:ℂ)*I) s)
      ((volume.restrict (Ioi 0)).prod (volume.prod volume)) := by
    apply hTimeM.aestronglyMeasurable.congr
    filter_upwards [hPos] with p hp
    unfold a03ZeroModeGCDInitialDensity
    rw [a03ZeroModeGCDArchKernel_eq_time hΦ hSupp hT σ hg ha hb hp (by linarith)]
  apply hmajorant.mono' hMeas
  filter_upwards [hPos] with p hp
  let u : ℂ := (ε:ℂ)+(p.2.1:ℂ)*I
  let v : ℂ := (ε:ℂ)+(p.2.2:ℂ)*I
  have hAr := hArch T hT σ g a b hg ha hb p.1 hp s rfl
  simp only [pow_zero,one_mul] at hAr
  have hYeq : Y=T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)) := by
    dsimp only [Y]
    rw [a03ZeroModeRatioPhysicalScale_eq,Nat.cast_mul]
  rw [←hYeq] at hAr
  have hK := hKernel p.2.1 p.2.2
  have hPhys : ‖a03ZeroModeRatioPhysicalKernel α g a b A B p.1 u v s‖≤
      ‖a03ZeroModeRatioPhysicalPrefactor α g a b A B p.1 s‖*
        ((p.1/(g*a:ℕ))^ε*(p.1/(g*b:ℕ))^ε)*(C*G p.2.1*G p.2.2) := by
    rw [a03ZeroModeRatioPhysicalKernel_eq_weighted α hg ha hb A B hp]
    unfold a03ZeroModeRatioWeightedKernel
    rw [norm_mul,norm_mul,a03ZeroModeRatioExponential_norm]
    have he : Real.exp (a03ZeroModeRatioPhysicalLogLeft g a p.1*u.re+a03ZeroModeRatioPhysicalLogRight g b p.1*v.re)=
        (p.1/(g*a:ℕ))^ε*(p.1/(g*b:ℕ))^ε := by
      simp only [u,v,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]
      rw [←add_mul,a03ZeroModeRatioPhysicalLogPair_exp hg ha hb hp]
    rw [he]
    convert mul_le_mul_of_nonneg_left hK
      (by positivity : 0≤‖a03ZeroModeRatioPhysicalPrefactor α g a b A B p.1 s‖*
        ((p.1/(g*a:ℕ))^ε*(p.1/(g*b:ℕ))^ε)) using 1
    ring
  have hEnv := a03ZeroModeRatioXEnvelope_nonneg Y p.1
  unfold a03ZeroModeGCDInitialDensity
  rw [norm_mul,norm_mul]
  calc
    _≤‖(p.1:ℂ)⁻¹‖*(D*(1+polarGaussianConstant T σ 1)*(p.1/T)^s.re*a03ZeroModeRatioXEnvelope Y p.1)*
      (‖a03ZeroModeRatioPhysicalPrefactor α g a b A B p.1 s‖*((p.1/(g*a:ℕ))^ε*(p.1/(g*b:ℕ))^ε)*
        (C*G p.2.1*G p.2.2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hAr (norm_nonneg _)) hPhys (norm_nonneg _) (by positivity)
    _=C0*P p.1*G p.2.1*G p.2.2 := by
      dsimp only [C0,P]
      have hxpow := a03ZeroModeGCDEtaResidual_density_power hT hp (cs := s.re)
      calc
        _=(D*(1+polarGaussianConstant T σ 1)*C)*
          (‖(p.1:ℂ)⁻¹‖*(p.1/T)^s.re)*
          (‖a03ZeroModeRatioPhysicalPrefactor α g a b A B p.1 s‖*((p.1/(g*a:ℕ))^ε*(p.1/(g*b:ℕ))^ε)*
            a03ZeroModeRatioXEnvelope Y p.1)*G p.2.1*G p.2.2 := by ring
        _=_ := by rw [hxpow]; ring

end
end Sechstmoment.Source
