import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.ActualBranchArchEnvelope
import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.ResidualAggregate

/-! Genuine actual leading original/dual profile wrappers for the full
positive-X ratio-contour remainder, uniformly on the original shift set. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeGCDEtaResidualX_supported_profile_integral_bound
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T η Ca Cr : ℝ} (hT : 1≤T) (hη : 0<η) (hη1 : η≤1/16) (hCa : 0≤Ca) (hCr : 0≤Cr)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤η/32)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {s : ℂ} (hs : s.re=1+η/4)
    (hArch : ∀ x : ℝ,0<x → (1+|s.im|)^2*‖a03ZeroModeGCDArchKernel Φ T σ g a b x s‖≤
      Ca*(1+polarGaussianConstant T σ 1)*(x/T)^(1+η/4)*
        a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x)
    (hRes : ∀ x : ℝ,0<x → ‖a03ZeroModeRatioPhysicalResidual (η/4) α g a b A B x s‖≤
      Cr*(Real.log T)^8*‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖*(a:ℝ)^(η/4)*(b:ℝ)^(η/4)*
        ((x/(g*a:ℕ))^(a03ZeroModeRatioPrimaryLine (η/4))*(x/(g*b:ℕ))^(a03ZeroModeRatioPrimaryLine (η/4))+
         (x/(g*b:ℕ))^(a03ZeroModeRatioSecondaryLine (η/4))+(x/(g*a:ℕ))^(a03ZeroModeRatioSecondaryLine (η/4)))) :
    IntegrableOn (fun x : ℝ => (x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
      a03ZeroModeRatioPhysicalResidual (η/4) α g a b A B x s) (Ioi 0) ∧
    T*(1+|s.im|)^2*‖a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B s‖≤
      5*Ca*Cr*(1+polarGaussianConstant T σ 1)*(Real.log T)^8*
        ‖A (g*a)‖*‖B (g*b)‖*T^(1/2+η)*a03ZeroModeRatioPrimitiveResidualPower g a b η := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hCG := polarGaussianConstant_nonneg T σ 1
  let F : ℝ→ℂ := fun x => (x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
    a03ZeroModeRatioPhysicalResidual (η/4) α g a b A B x s
  let W : ℝ := T*(1+|s.im|)^2
  have hW : 0<W := by dsimp [W]; positivity
  let Q : ℝ := T*Ca*Cr*(1+polarGaussianConstant T σ 1)*(Real.log T)^8*T^(-(1+η/4))
  have hQ : 0≤Q := by dsimp [Q]; positivity
  let J : Fin 3→ℝ→ℝ := fun j => a03ZeroModeRatioPhysicalXMajorant T (η/4) (η/4) (1+η/4) α g a b A B s j
  have hJ (j : Fin 3) : IntegrableOn (J j) (Ioi 0) :=
    (a03ZeroModeRatioPhysicalXMajorant_integrable_and_mass hTp hη hη1 α hα hg ha hb A B s j).1
  have hSum : IntegrableOn (fun x => ∑ j : Fin 3,J j x) (Ioi 0) := integrable_finsetSum _ (fun j _ => hJ j)
  have hpoint : ∀ x : ℝ,0<x → ‖(W:ℂ)*F x‖≤Q*(∑ j : Fin 3,J j x) := by
    intro x hx
    have hEnv := a03ZeroModeRatioXEnvelope_nonneg (a03ZeroModeRatioPhysicalScale T g a b) x
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hW.le]
    dsimp only [F]
    rw [norm_mul,norm_mul]
    calc
      _=(T*‖(x:ℂ)⁻¹‖)*((1+|s.im|)^2*‖a03ZeroModeGCDArchKernel Φ T σ g a b x s‖)*
        ‖a03ZeroModeRatioPhysicalResidual (η/4) α g a b A B x s‖ := by dsimp [W]; ring
      _≤(T*‖(x:ℂ)⁻¹‖)*
        (Ca*(1+polarGaussianConstant T σ 1)*(x/T)^(1+η/4)*
          a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x)*
        (Cr*(Real.log T)^8*‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖*(a:ℝ)^(η/4)*(b:ℝ)^(η/4)*
          ((x/(g*a:ℕ))^(a03ZeroModeRatioPrimaryLine (η/4))*(x/(g*b:ℕ))^(a03ZeroModeRatioPrimaryLine (η/4))+
           (x/(g*b:ℕ))^(a03ZeroModeRatioSecondaryLine (η/4))+(x/(g*a:ℕ))^(a03ZeroModeRatioSecondaryLine (η/4)))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hArch x hx) (by positivity)) (hRes x hx)
            (norm_nonneg _) (by positivity)
      _=Q*(∑ j : Fin 3,J j x) := by
        dsimp only [Q,J]
        rw [a03ZeroModeRatioPhysicalXMajorant_sum]
        have hp := a03ZeroModeGCDEtaResidual_density_power hTp hx (cs := 1+η/4)
        calc
          _=(T*Ca*Cr*(1+polarGaussianConstant T σ 1)*(Real.log T)^8)*
            (‖(x:ℂ)⁻¹‖*(x/T)^(1+η/4))*
            (‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖*(a:ℝ)^(η/4)*(b:ℝ)^(η/4)*
              ((x/(g*a:ℕ))^(a03ZeroModeRatioPrimaryLine (η/4))*(x/(g*b:ℕ))^(a03ZeroModeRatioPrimaryLine (η/4))+
               (x/(g*b:ℕ))^(a03ZeroModeRatioSecondaryLine (η/4))+(x/(g*a:ℕ))^(a03ZeroModeRatioSecondaryLine (η/4)))*
                a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x) := by ring
          _=_ := by rw [hp]; ring
  have hMeas : AEStronglyMeasurable F (volume.restrict (Ioi 0)) :=
    (((Complex.measurable_ofReal.inv).aestronglyMeasurable.restrict).mul
      (a03ZeroModeGCDArchKernel_aestronglyMeasurable hΦ hSupp hTp σ hg ha hb (by linarith))).mul
        (a03ZeroModeRatioPhysicalResidual_measurable_comp (η/4) α g ha.ne' hb.ne' A B measurable_id measurable_const).aestronglyMeasurable.restrict
  have hWeighted : IntegrableOn (fun x => (W:ℂ)*F x) (Ioi 0) :=
    (hSum.const_mul Q).mono' (hMeas.const_mul _) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hpoint x hx)
  have hF : IntegrableOn F (Ioi 0) :=
    (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hW.ne')) F).mp hWeighted
  refine ⟨hF,?_⟩
  have hNorm := norm_integral_le_of_norm_le (f := fun x => (W:ℂ)*F x) (hSum.const_mul Q)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx; exact hpoint x hx)
  rw [integral_const_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hW.le,
    integral_const_mul,integral_finsetSum _ (fun j _ => hJ j)] at hNorm
  change W*‖a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B s‖≤_ at hNorm
  apply hNorm.trans
  have hm (j : Fin 3) := a03ZeroModeRatioPhysicalXMajorant_total_budget hT hη hη1 α hα hg ha hb A B hs j
  calc
    _=(Ca*Cr*(1+polarGaussianConstant T σ 1)*(Real.log T)^8)*
      (∑ j : Fin 3,T*T^(-(1+η/4))*(∫x in Ioi (0:ℝ),J j x)) := by
        dsimp [Q]
        rw [←Finset.mul_sum]
        ring
    _≤(Ca*Cr*(1+polarGaussianConstant T σ 1)*(Real.log T)^8)*
      (∑ j : Fin 3,5*‖A (g*a)‖*‖B (g*b)‖*T^(1/2+η)*(g:ℝ)^(-1:ℝ)*
        (a:ℝ)^(a03ZeroModeRatioResidualAmplifierLeftExponent η j-1)*
        (b:ℝ)^(a03ZeroModeRatioResidualAmplifierRightExponent η j-1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun j _ => hm j)
    _=_ := by
      unfold a03ZeroModeRatioPrimitiveResidualPower
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem a03ZeroModeGCDEtaResidualX_actual_branch_chambers_uniform_integrated_bound
    (K : Set MomentShifts) (hK : IsCompact K) {κ η : ℝ}
    (hκ : 0<κ) (hη : 0<η) (hη1 : η≤1/16)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ dual m n : Bool,
      ∀ g a b : ℕ,0<g → 0<a → 0<b → ∀ A B : ℕ→ℂ,∀ s : ℂ,s.re=1+η/4 →
        let α := rawMomentShifts T (Sechstmoment.a03SourceNormalizedChamber dual m n σ)
        IntegrableOn (fun x : ℝ => (x:ℂ)⁻¹*a03ZeroModeGCDArchKernel (Sechstmoment.a03RatioLeadingBranchProfile dual Φ T σ) T σ g a b x s*
          a03ZeroModeRatioPhysicalResidual (η/4) α g a b A B x s) (Ioi 0) ∧
        T*(1+|s.im|)^2*‖a03ZeroModeGCDEtaResidualX (Sechstmoment.a03RatioLeadingBranchProfile dual Φ T σ) T σ (η/4) α g a b A B s‖≤
          C*(Real.log T)^56*‖A (g*a)‖*‖B (g*b)‖*T^(1/2+η)*
            a03ZeroModeRatioPrimitiveResidualPower g a b η := by
  have hε : 0<η/4 := by positivity
  have hε1 : η/4<1/8 := by linarith
  have hcs : 1+η/4∈Icc (1/8:ℝ) (15/8) := by constructor <;> linarith
  obtain ⟨Ca,hCa,hArch⟩ := a03ZeroModeGCDArchKernel_actual_branch_full_height_envelope hΦ hSupp K hK hcs 2
  obtain ⟨Cr,hCr,hRes⟩ := a03ZeroModeRatioPhysicalResidual_chambers_uniform_log_bound K hK hκ hε hε1 hε hroot
  let P : ℝ := Real.exp 1*2^48*(1+1/κ^2)^24
  have hP : 0≤P := by dsimp [P]; positivity
  let C : ℝ := 5*Ca*Cr*(1+P)
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  let W := a03SourceNormalizedChambersCompactSet K
  have hW := a03SourceNormalizedChambersCompactSet_isCompact K hK
  filter_upwards [hArch,hRes,compactNormalizedShifts_eventually_norm_small W hW (η/32) (by positivity),
    eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
      with T hArch hRes hsmall hT hlog
  intro σ hσ dual m n g a b hg ha hb A B s hs
  let α := rawMomentShifts T (Sechstmoment.a03SourceNormalizedChamber dual m n σ)
  have hmem : Sechstmoment.a03SourceNormalizedChamber dual m n σ∈W :=
    mem_iUnion.mpr ⟨(dual,(m,n)),⟨σ,hσ,rfl⟩⟩
  have hα : ∀ j : Fin 4,‖α j‖≤η/32 := hsmall _ hmem
  have hRs (x : ℝ) (hx : 0<x) := hRes dual m n σ hσ g a b hg ha hb A B x hx s (by linarith : 1+η/4≤s.re)
  simp_rw [←Sechstmoment.a03SourceNormalizedChamber_raw] at hRs
  have hYeq : a03ZeroModeRatioPhysicalScale T g a b=T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)) := by
    rw [a03ZeroModeRatioPhysicalScale_eq,Nat.cast_mul]
  have hAs (x : ℝ) (hx : 0<x) := hArch σ hσ dual g a b hg ha hb x hx s hs
  rw [←hYeq] at hAs
  obtain ⟨hi,hbound⟩ := a03ZeroModeGCDEtaResidualX_supported_profile_integral_bound
    (Sechstmoment.a03RatioLeadingBranchProfile_contDiff hΦ hSupp (zero_lt_one.trans hT) σ dual)
    ((Sechstmoment.a03RatioLeadingBranchProfile_support dual Φ T σ).trans hSupp) hT.le hη hη1 hCa hCr
    σ α hα hg ha hb A B hs hAs hRs
  refine ⟨hi,hbound.trans ?_⟩
  have hp := polarGaussianConstant_log_growth hT hlog hκ σ (hroot σ hσ)
  have hL : 1≤(Real.log T)^48 := by
    exact one_le_pow₀ hlog
  have hCG : 1+polarGaussianConstant T σ 1≤(1+P)*(Real.log T)^48 := by
    change polarGaussianConstant T σ 1≤P*(Real.log T)^48 at hp
    nlinarith
  have hpower : 0≤a03ZeroModeRatioPrimitiveResidualPower g a b η := by
    unfold a03ZeroModeRatioPrimitiveResidualPower
    positivity
  calc
    _≤5*Ca*Cr*((1+P)*(Real.log T)^48)*(Real.log T)^8*
      ‖A (g*a)‖*‖B (g*b)‖*T^(1/2+η)*a03ZeroModeRatioPrimitiveResidualPower g a b η := by
        gcongr
    _=_ := by dsimp [C]; ring

end
end Sechstmoment.Source
