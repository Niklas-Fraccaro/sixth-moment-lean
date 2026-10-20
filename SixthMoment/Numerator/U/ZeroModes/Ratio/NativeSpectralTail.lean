import SixthMoment.Numerator.U.Replacement.VStar.PhysicalTailRapidNormalized
import SixthMoment.Numerator.U.ZeroModes.NativeFamilyMass
import SixthMoment.Numerator.U.ZeroModes.Ratio.FullVStarNative
import SixthMoment.Numerator.U.ZeroModes.UnsortedActualMass

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 300000

theorem a03SourceSpectralActualRatioLinearZero_tail_eq_physical
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hlog : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ α : MomentShifts) (hroot : ∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hα : ∀j,‖α j‖≤1/4) (dual : Bool) (tM tN r s L : ℝ)
    (m n : Bool) (q : QuadraticScales) (hq : ∀j,0<q.size j) (a b : ℕ→ℂ) :
    (1/(2*Real.pi):ℂ)*(∫v : ℝ in {v : ℝ | L < |v|},
      a03SourceSpectralActualRatioLinearZero dual Φ T c σ α tM tN r s m n q a b v)=
      a03PhysicalSpectralSetNativeLinearZero (a03RatioLeadingBranchProfile dual Φ T σ) T c σ α r s
        (a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN) m n q a b {v : ℝ | L < |v|} := by
  simp_rw [a03SourceSpectralActualRatioLinearZero_eq_native]
  exact a03SourceSpectralNativeLinearZero_set_eq_physical
    (a03RatioLeadingBranchProfile_continuous hΦ hSupp (zero_lt_one.trans hT) σ dual)
    ((a03RatioLeadingBranchProfile_support dual Φ T σ).trans hSupp)
    (zero_lt_one.trans hT) hc σ α hα r s _
    (a03RatioEuclideanMultiplier_contDiff _ _ _).continuous.measurable
    (a03ActualRatioMultiplier_norm_le hT hlog hκ σ hroot tM tN) m n q hq a b _

theorem a03SourceSpectralActualRatioLinearZero_core_sub_VStar_eq_neg_tail
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c κ : ℝ} (hT : 1<T) (hlog : 1≤Real.log T) (hc : 0<c) (hκ : 0<κ)
    (σ α : MomentShifts) (hroot : ∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (hα : ∀j,‖α j‖≤1/4) (dual : Bool) (tM tN r s L : ℝ)
    (m n : Bool) (q : QuadraticScales) (hq : ∀j,0<q.size j) (a b : ℕ→ℂ) :
    (1/(2*Real.pi):ℂ)*(∫v : ℝ in Icc (-L) L,
      a03SourceSpectralActualRatioLinearZero dual Φ T c σ α tM tN r s m n q a b v)-
      a03PhysicalActualRatioLinearVStarZeroMode dual Φ T σ α tM tN r s m n q a b=
      -(1/(2*Real.pi):ℂ)*(∫v : ℝ in {v : ℝ | L < |v|},
        a03SourceSpectralActualRatioLinearZero dual Φ T c σ α tM tN r s m n q a b v) := by
  have hquad : ∀j,0<a03ZeroModeQuadScales (phasePairSwapScales m n q) j := by
    intro j
    cases m <;> cases n <;> fin_cases j <;>
      simp [a03ZeroModeQuadScales,phasePairSwapScales] <;>
      first | exact hq 2 | exact hq 3 | exact hq 4 | exact hq 5
  rw [←a03SourceSpectralActualRatioLinearZero_full_eq_VStar hΦ hSupp hT hlog hc hκ σ α hroot hα
    dual tM tN r s m n q hq a b]
  simp_rw [a03SourceSpectralActualRatioLinearZero_eq_native]
  exact a03SourceSpectralNativeLinearZero_core_sub_full_eq_neg_tail
    (a03RatioLeadingBranchProfile_continuous hΦ hSupp (zero_lt_one.trans hT) σ dual)
    ((a03RatioLeadingBranchProfile_support dual Φ T σ).trans hSupp)
    (zero_lt_one.trans hT) hc σ α hα r s L _
    (a03RatioEuclideanMultiplier_contDiff _ _ _).continuous.measurable
    (a03ActualRatioMultiplier_norm_le hT hlog hκ σ hroot tM tN) m n q
    (by simpa [QuadraticScales.size] using hq 3) hquad a b

theorem a03_actual_ratio_native_spectral_tail_uniform_mass_bound
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c θ κ R u : ℝ} (hc : 0<c) (hθ : 0<θ) (hκ : 0<κ) (hR : 0≤R) (N : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀j,‖σ j‖≤R) → (∀j,‖α j‖≤1/4) → (∀j,‖α j‖≤R/Real.log T) →
      (∀j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ dual : Bool,∀ tM tN r s : ℝ,∀ m n : Bool,∀ q : QuadraticScales,
      (∀j,0<q.size j) → 1≤q.M₂ → 1≤q.N₂ → q.M*q.N≤T^(2+u) →
      ∀ a b : ℕ→ℂ,∀ A B : ℝ,0≤A → 0≤B →
      (∀j : ℕ,0<j → ‖a j‖≤A/Real.sqrt (j:ℝ)) →
      (∀j : ℕ,0<j → ‖b j‖≤B/Real.sqrt (j:ℝ)) →
      ‖(1/(2*Real.pi):ℂ)*(∫v : ℝ in {v : ℝ | θ*Real.log T < |v|},
        a03SourceSpectralActualRatioLinearZero dual Φ T c σ α tM tN r s m n q a b v)‖≤
        A*B*C*T^(-N)*a03ZeroModeLiteralMass q := by
  obtain ⟨C,hC,hpoint⟩ := a03VStarPhysicalTimeTail_normalized_uniform_rapid
    (η:=u) hΦ hSupp hc hθ hκ hR (N+1)
  let K := a03RatioMultiplierDerivativeBudget κ 0
  have hK := a03RatioMultiplierDerivativeBudget_nonneg κ 0
  have hlog8 : ∀ᶠ T : ℝ in atTop,(Real.log T)^8≤T := by
    have h := (log_pow_isLittleO_rpow 8 (δ:=1) zero_lt_one).bound zero_lt_one
    filter_upwards [h,eventually_gt_atTop (1:ℝ)] with T h hT
    simpa only [Real.rpow_one,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hT),
      abs_of_nonneg (by positivity : 0≤(Real.log T)^8),one_mul] using h
  refine ⟨K*C,by positivity,?_⟩
  filter_upwards [hpoint,hlog8,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hpoint hlog8 hT hlog
  intro σ α hσ hα hαnorm hroot dual tM tN r s m n q hq hM₂ hN₂ hprod a b A B hA hB ha hb
  have hTp : 0<T := zero_lt_one.trans hT
  let G := a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN
  let Ψ := a03RatioLeadingBranchProfile dual Φ T σ
  let F : (Fin 5→ℕ)→ℝ→ℂ := fun w x =>
    let y := a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x)
    G y*a03PhysicalLeadingFourierSet Ψ c T σ α (a03ZeroModePermutedPhysicalQuad m n q w x)
      (T*s*r*Real.exp (a03SixGapLinear y)) {v : ℝ | θ*Real.log T < |v|}
  have hF (w : Fin 5→ℕ) (hw : w∈quadraticMainIndexSet q) (x : ℝ) (hx : 0<x)
      (hω : a03ZeroModeSmoothProduct q w x≠0) :
      ‖F w x‖≤(K*C*T^(-N))/Real.sqrt (∏ j : Fin 4,a03ZeroModePhysicalQuad q w x j) := by
    let y := a03SixTensorLogPoint (a03SixZeroSourceArguments m n q w x)
    let Q := a03ZeroModePermutedPhysicalQuad m n q w x
    have hmask := a03ZeroModePhysicalQuad_nonzero_mask_bounds q hq hM₂ hN₂ w hw x hω
    have hQ := a03ZeroModePermutedPhysicalQuad_lower m n q w x hmask.1
    have hcut : (∏j : Fin 4,Q j)≤16*T^(2+u) := by
      rw [a03ZeroModePermutedPhysicalQuad_product]
      exact hmask.2.trans (mul_le_mul_of_nonneg_left hprod (by norm_num))
    have ht := hpoint σ hσ hroot α hαnorm Q hQ hcut dual (T*s*r*Real.exp (a03SixGapLinear y))
    have he := a03PhysicalLeadingFourierSet_time_eq
      (a03RatioLeadingBranchProfile_continuous hΦ hSupp hTp σ dual)
      ((a03RatioLeadingBranchProfile_support dual Φ T σ).trans hSupp) hTp hc σ α Q
      (fun j => zero_lt_one.trans_le (hQ j)) (T*s*r*Real.exp (a03SixGapLinear y))
      {v : ℝ | θ*Real.log T < |v|}
    have hΨ : Ψ=a03VStarBranchTimeProfile dual Φ T σ := by cases dual <;> rfl
    change a03PhysicalLeadingFourierSet Ψ c T σ α Q _ _=a03VStarPhysicalTimeTail dual Φ c T σ α Q _ _ at he
    rw [a03ZeroModePermutedPhysicalQuad_product] at ht
    have hg := a03ActualRatioMultiplier_norm_le hT hlog hκ σ hroot tM tN y
    change ‖G y*a03PhysicalLeadingFourierSet Ψ c T σ α Q _ _‖≤_
    rw [norm_mul,he]
    calc
      _≤(K*(Real.log T)^8)*(C*T^(-(N+1))/Real.sqrt (∏j : Fin 4,a03ZeroModePhysicalQuad q w x j)) :=
        mul_le_mul hg ht (norm_nonneg _) (by positivity)
      _≤(K*T)*(C*T^(-(N+1))/Real.sqrt (∏j : Fin 4,a03ZeroModePhysicalQuad q w x j)) := by gcongr
      _=_ := by
        have hp : T*T^(-(N+1))=T^(-N) := by
          calc
            _=T^(1:ℝ)*T^(-(N+1)) := by rw [Real.rpow_one]
            _=T^(1+(-(N+1))) := (Real.rpow_add hTp _ _).symm
            _=_ := by congr 1; ring
        rw [show K*T*(C*T^(-(N+1))/Real.sqrt (∏j : Fin 4,a03ZeroModePhysicalQuad q w x j))=
          K*C*(T*T^(-(N+1)))/Real.sqrt (∏j : Fin 4,a03ZeroModePhysicalQuad q w x j) by ring,hp]
  rw [a03SourceSpectralActualRatioLinearZero_tail_eq_physical hΦ hSupp hT hlog hc hκ σ α hroot hα
    dual tM tN r s (θ*Real.log T) m n q hq a b]
  have hbound := a03NativePhysicalZeroFamily_mass_bound F m n q (by linarith) a b hA hB
    (show 0≤K*C*T^(-N) by positivity) ha hb hF
  convert hbound using 1
  · congr 1
    unfold a03PhysicalSpectralSetNativeLinearZero F
    apply Finset.sum_congr rfl
    intro w _
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by dsimp only; ring
  · ring

end
end SixthMoment
