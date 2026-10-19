import Sechstmoment.Numerator.U.ZeroModes.PassiveZeroModeUnsortedLinearBound
import Sechstmoment.Numerator.U.ZeroModes.Ratio.ZeroReplacementBound

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_passive_ratio_zero_symbols_uniform_mass_bound
    {a b s : ℝ} (hs0 : 0≤s) (hs : s<1) (f g : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) → (∀ j,‖α j‖≤R/Real.log T) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ A B H : ℝ,0<A → 0<B → 0<H → ∀ k : Fin 4→ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+η)) → k 1≠0 → k 3≠0 →
      A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ linear dual positive : Bool,∀ tM tN : ℝ,
      let p := phaseActualNearTensorData T σ α v A B H k positive
      ‖(T:ℂ)*a03SourceMellinScaleFactor c v α k*
        a03EndpointPhysicalUnsortedZeroMode
          (fun y => a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN y*
            a03RatioZeroErrorSymbol linear dual Φ c p y) T A B H f g k‖≤
          C*(Real.log T)^8*T^(2*s+ε)*a03ZeroModeLiteralMass (phaseActualScales A B H k) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨C,hC,hmain⟩ := a03_zero_replacement_unsorted_kernel_uniform_physical_density
    (η:=η) hΦ hΦs hc hc1 hε hκ hθ hR
  obtain ⟨D,hD,hlin⟩ := a03_passive_zero_linearization_unsorted_kernel_uniform_physical_density
    (η:=η) hs f g hΦ hΦs hc hc1 hε hκ hθ hR
  let K := a03RatioMultiplierDerivativeBudget κ 0
  have hK : 0≤K := a03RatioMultiplierDerivativeBudget_nonneg κ 0
  refine ⟨F*G*(C+D)*K,by positivity,?_⟩
  filter_upwards [hmain,hlin,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hmain hlin hT hlog
  intro σ α hσ hα hαnorm hroot A B H hA hB hH k hk hk1 hk3 hactive v hv linear dual positive tM tN
  dsimp only
  let p := phaseActualNearTensorData T σ α v A B H k positive
  let q := phaseActualScales A B H k
  let Rg := a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN
  have hTp : 0<T := zero_lt_one.trans hT
  have hM₂ : 0<q.M₂ := boundaryActual_scale_pos _
  have hpoint (w : Fin 5→ℕ) (hw : w∈quadraticMainIndexSet q) (x : ℝ) (hx : 0<x)
      (hω : a03ZeroModeSmoothProduct q w x≠0) :
      ‖a03SourceMellinScaleFactor c v α k*
        (Rg (a03SixTensorLogPoint (a03SixZeroSourceArguments false false q w x))*
          a03RatioZeroCutoffErrorSymbol linear dual Φ c p
            (a03SixTensorLogPoint (a03SixZeroSourceArguments false false q w x)))‖≤
        ((C+D)*K*(Real.log T)^8*T^(2*s-1+ε))/Real.sqrt (∏ j : Fin 4,a03ZeroModePhysicalQuad q w x j) := by
    let y := a03SixTensorLogPoint (a03SixZeroSourceArguments false false q w x)
    have hraw : ‖a03SourceMellinScaleFactor c v α k*a03RatioZeroCutoffErrorSymbol linear dual Φ c p y‖≤
        (C+D)*T^(2*s-1+ε)/Real.sqrt (∏ j : Fin 4,a03ZeroModePhysicalQuad q w x j) := by
      cases linear
      · have hb := hmain σ hσ hroot α hα hαnorm A B H hA hB hH k hk hk1 hk3 v hv dual positive w hw x hx hω
        apply hb.trans
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact mul_le_mul (le_add_of_nonneg_right hD)
          (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith)) (by positivity) (by positivity)
      · have hb := hlin σ hσ hroot α hα hαnorm A B H hA hB hH k hk hk1 hk3 hactive v hv dual positive w hw x hx hω
        apply hb.trans
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (by positivity)) (Real.sqrt_nonneg _)
    have hr := a03ActualRatioMultiplier_norm_le hT hlog hκ σ hroot tM tN y
    have he : a03SourceMellinScaleFactor c v α k*(Rg y*a03RatioZeroCutoffErrorSymbol linear dual Φ c p y)=
        Rg y*(a03SourceMellinScaleFactor c v α k*a03RatioZeroCutoffErrorSymbol linear dual Φ c p y) := by ring
    change ‖a03SourceMellinScaleFactor c v α k*(Rg y*a03RatioZeroCutoffErrorSymbol linear dual Φ c p y)‖≤_
    rw [he,norm_mul]
    exact (mul_le_mul hr hraw (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hb := a03SixTensorPhysicalZeroMode_norm_le_literal_mass
    (fun y => Rg y*a03RatioZeroCutoffErrorSymbol linear dual Φ c p y)
    (a03SourceMellinScaleFactor c v α k) false false q hM₂
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
    hF hG (show 0≤(C+D)*K*(Real.log T)^8*T^(2*s-1+ε) by positivity)
    (fun j hj => phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt T A f hF hfb hj)
    (fun j hj => phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt T B g hG hgb hj) hpoint
  have he : a03SixTensorPhysicalZeroMode (fun y => Rg y*a03RatioZeroCutoffErrorSymbol linear dual Φ c p y)
      false false q (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)=
      a03SixTensorPhysicalZeroMode (fun y => Rg y*a03RatioZeroErrorSymbol linear dual Φ c p y)
        false false q (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B) := by
    cases linear
    · rfl
    · apply a03SixTensorPhysicalZeroMode_congr_on_dyadic_box _ _ false false q hB _ _
        (phaseActualAmplifierCoefficient_support T g hB)
      intro x hx
      simp only [a03RatioZeroCutoffErrorSymbol,a03RatioZeroErrorSymbol,ite_true,
        a03ZeroModeCutoffLinearizationKernel,a03TensorLogCutoff_logPoint_one hx,one_mul]
  rw [he] at hb
  rw [mul_assoc,norm_mul,Complex.norm_real,Real.norm_of_nonneg hTp.le]
  change T*‖a03SourceMellinScaleFactor c v α k*
    a03SixTensorPhysicalZeroMode (fun y => Rg y*a03RatioZeroErrorSymbol linear dual Φ c p y)
      false false q (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)‖≤_
  apply (mul_le_mul_of_nonneg_left hb hTp.le).trans_eq
  rw [show T*(F*G*((C+D)*K*(Real.log T)^8*T^(2*s-1+ε))*a03ZeroModeLiteralMass q)=
    (F*G*(C+D)*K)*(Real.log T)^8*(T^(1:ℝ)*T^(2*s-1+ε))*a03ZeroModeLiteralMass q by
      rw [Real.rpow_one]; ring,←Real.rpow_add hTp]
  congr 2
  ring

theorem a03_actual_passive_ratio_Gamma_zero_sub_linear_uniform_mass_bound
    {a b s : ℝ} (hs0 : 0≤s) (hs : s<1) (f g : ℝ→ℝ)
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j,‖α j‖≤1/4) → (∀ j,‖α j‖≤R/Real.log T) →
      (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ A B H : ℝ,0<A → 0<B → 0<H → ∀ k : Fin 4→ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+η)) → k 1≠0 → k 3≠0 →
      A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual positive : Bool,∀ tM tN : ℝ,
      let p := phaseActualNearTensorData T σ α v A B H k positive
      ‖(T:ℂ)*a03SourceMellinScaleFactor c v α k*
        (a03EndpointPhysicalUnsortedZeroMode
          (a03RatioSourceRawFamilyKernel dual Φ c tM tN p) T A B H f g k-
            a03EndpointPhysicalUnsortedZeroMode
              (a03RatioSourceLinearRawFamilyKernel dual Φ c tM tN p) T A B H f g k)‖≤
          C*(Real.log T)^8*T^(2*s+ε)*a03ZeroModeLiteralMass (phaseActualScales A B H k) := by
  obtain ⟨C,hC,hbound⟩ := a03_actual_passive_ratio_zero_symbols_uniform_mass_bound
    (η:=η) hs0 hs f g hf hg hΦ hΦs hc hc1 hε hκ hθ hR
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hbound,a03_actual_ratio_zero_eventually_sub_linear_eq_symbols hΦ hΦs hc hc1 hκ hθ hR]
    with T hbound heq
  intro σ α hσ hα hαnorm hroot A B H hA hB hH k hk hk1 hk3 hactive v hv dual positive tM tN
  dsimp only
  let p := phaseActualNearTensorData T σ α v A B H k positive
  let q := phaseActualScales A B H k
  let G := a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN
  have he := heq σ α hσ hα hroot v hv dual p.r p.s tM tN false false q
    (boundaryActual_scale_pos _) (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
  have he' : a03EndpointPhysicalUnsortedZeroMode (a03RatioSourceRawFamilyKernel dual Φ c tM tN p) T A B H f g k-
      a03EndpointPhysicalUnsortedZeroMode (a03RatioSourceLinearRawFamilyKernel dual Φ c tM tN p) T A B H f g k=
      a03EndpointPhysicalUnsortedZeroMode (fun y => G y*a03RatioZeroErrorSymbol false dual Φ c p y) T A B H f g k+
        a03EndpointPhysicalUnsortedZeroMode (fun y => G y*a03RatioZeroErrorSymbol true dual Φ c p y) T A B H f g k := by
    exact he
  rw [he',mul_add]
  have h1 := hbound σ α hσ hα hαnorm hroot A B H hA hB hH k hk hk1 hk3 hactive v hv false dual positive tM tN
  have h2 := hbound σ α hσ hα hαnorm hroot A B H hA hB hH k hk hk1 hk3 hactive v hv true dual positive tM tN
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end
end Sechstmoment
