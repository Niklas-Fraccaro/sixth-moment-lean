import Sechstmoment.Numerator.U.ZeroModes.UnsortedReplacementBound

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_zero_linearization_unsorted_kernel_uniform_physical_density
    {s : ℝ} (hs : s<1) (f g : ℝ→ℝ)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ α : MomentShifts,(∀ j,‖α j‖≤1/4) → (∀ j,‖α j‖≤R/Real.log T) → ∀ A B H : ℝ,0<A → 0<B → 0<H → ∀ k : Fin 4→ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+η)) → k 1≠0 → k 3≠0 →
      phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual positive : Bool,
      let p := phaseActualNearTensorData T σ α v A B H k positive
      let q := phaseActualScales A B H k
      let m := false
      let n := false
      let qs := q
      ∀ w∈quadraticMainIndexSet qs,∀ x : ℝ,0<x → a03ZeroModeSmoothProduct qs w x≠0 →
        ‖a03SourceMellinScaleFactor c v α k*
          a03ZeroModeCutoffLinearizationKernel dual Φ c p
            (a03SixTensorLogPoint (a03SixZeroSourceArguments m n qs w x))‖≤
          C*T^(2*s-1+ε)/Real.sqrt (∏ i : Fin 4,a03ZeroModePhysicalQuad qs w x i) := by
  obtain ⟨C,hC,hfreq⟩ := a03_leading_frequency_uniform_lipschitz hΦ hΦs hc hc1 hε hκ hθ hR
  let D := Real.exp (R*(Real.log 16+(2+η)))
  have hsmall : ∀ᶠ T : ℝ in atTop,320*T^(s-1)≤1/2 := by
    have ht := (tendsto_rpow_neg_atTop (show 0<1-s by linarith)).const_mul 320
    have hh := ((tendsto_order.1 ht).2 (1/2) (by norm_num))
    simpa only [neg_sub,mul_zero] using hh.mono (fun _ h => h.le)
  refine ⟨204800*C*D,by positivity,?_⟩
  filter_upwards [hfreq,hsmall,eventually_gt_atTop (0:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hfreq hsmall hT hlog
  intro σ hσ hroot α hα hαnorm A B H hA hB hH k hk hk1 hk3 hactive v hv dual positive
  dsimp only
  let p := phaseActualNearTensorData T σ α v A B H k positive
  let q := phaseActualScales A B H k
  let m := false
  let n := false
  let qs := q
  have hpos (m n : Bool) : ∀ j,0<(phasePairSwapScales m n (phaseActualScales A B H k)).size j := by
    intro j
    cases m <;> cases n <;> fin_cases j <;>
      simp [phasePairSwapScales,phaseActualScales,QuadraticScales.size] <;>
      first | exact hA | exact hB | exact hH | exact boundaryActual_scale_pos _
  have hqs : ∀ j,0<qs.size j := hpos m n
  have hsg : |p.s|=1 := by cases positive <;> norm_num [p,phaseActualNearTensorData,rectangularGapSign]
  have hr : 0≤p.r := by
    dsimp [p,phaseActualNearTensorData]
    exact div_nonneg hH.le (mul_nonneg hB.le (mul_nonneg (boundaryActual_scale_pos _).le (boundaryActual_scale_pos _).le))
  have hrb : p.r≤16*T^(s-1) := phase_actual_near_relative_gap_scale T A B H _ f g hA hB hH k
    (Real.rpow_nonneg hT.le _) (by nlinarith [Real.rpow_nonneg hT.le (s-1)]) hactive
  have hsizes : 1≤qs.M₂ ∧ 1≤qs.N₂ :=
    ⟨rectangular_AFE_smooth_scale_ge_one (by omega),rectangular_AFE_smooth_scale_ge_one (by omega)⟩
  have hcut : qs.M*qs.N≤T^(2+η) := by
    simpa [qs,q,phaseActualScales,QuadraticScales.M,QuadraticScales.N,Fin.prod_univ_four,mul_assoc]
      using (Finset.mem_filter.mp hk).2
  intro w hw x hx hω
  let y := a03SixTensorLogPoint (a03SixZeroSourceArguments m n qs w x)
  change ‖a03SourceMellinScaleFactor c v α k*a03ZeroModeCutoffLinearizationKernel dual Φ c p y‖≤_
  by_cases hy : a03TensorLogCutoff y=0
  · simp only [a03ZeroModeCutoffLinearizationKernel,hy,mul_zero,zero_mul,norm_zero]
    positivity
  have hw1 (j : Fin 5) : 1≤w j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
  have hb := a03ZeroModePhysicalQuad_nonzero_mask_bounds qs hqs hsizes.1 hsizes.2 w hw x hω
  have hperm := a03ZeroModePermutedPhysicalQuad_lower m n qs w x hb.1
  have hpcut : (∏ i : Fin 4,a03ZeroModePermutedPhysicalQuad m n qs w x i)≤16*T^(2+η) := by
    rw [a03ZeroModePermutedPhysicalQuad_product]
    exact hb.2.trans (mul_le_mul_of_nonneg_left hcut (by norm_num))
  have hden := a03ZeroModeRealQuadDenominator_normalized_inv_norm_le hT hlog (by norm_num : (1:ℝ)≤16) hR
    α hαnorm ((c:ℂ)+(v:ℂ)*I) (by simpa using hc.le) _ hperm hpcut
  rw [a03ZeroModePermutedPhysicalQuad_product] at hden
  have hphase := a03_log_to_linear_frequency_cutoff_bound hT hr hrb hsg hsmall y hy
  have hff := hfreq σ α hσ hα hroot v hv dual
    (-a03RealLogGapSymbol T p.r p.s (a03SixGapLinear y)) (-T*p.s*p.r*Real.exp (a03SixGapLinear y))
  have hffb := hff.trans (mul_le_mul_of_nonneg_left hphase (by positivity : 0≤C*T^ε))
  have hscale0 := a03ZeroModeMellinScaleFactor_pair_actual m n A B H c v α k
  have hscale : a03ZeroModeMellinScaleFactor (phasePairSwapScales m n qs) α ((c:ℂ)+(v:ℂ)*I)=
      a03SourceMellinScaleFactor c v α k := by
    simpa only [m,n,qs,q,phasePairSwapScales,Bool.false_eq_true,ite_false] using hscale0
  have he : a03SourceMellinScaleFactor c v α k*a03ZeroModeCutoffLinearizationKernel dual Φ c p y=
      a03TensorLogCutoff y*(a03ZeroModeRealQuadDenominator α ((c:ℂ)+(v:ℂ)*I)
        (a03ZeroModePermutedPhysicalQuad m n qs w x))⁻¹*
      ((if dual then a03GaussianDualLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)
        (-a03RealLogGapSymbol T p.r p.s (a03SixGapLinear y)) else a03GaussianLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)
        (-a03RealLogGapSymbol T p.r p.s (a03SixGapLinear y)))-
        (if dual then a03GaussianDualLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)
        (-T*p.s*p.r*Real.exp (a03SixGapLinear y)) else a03GaussianLeadingFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)
        (-T*p.s*p.r*Real.exp (a03SixGapLinear y)))) := by
    rw [←a03ZeroMode_scale_mellin_eq_denominator m n qs hqs α _ w hw1 hx,hscale]
    cases dual <;> simp only [a03ZeroModeCutoffLinearizationKernel,a03ZeroModeLinearizationKernel,
      a03ZeroModeLeadingKernel,a03ZeroModeLinearKernel,ite_true,Bool.false_eq_true,ite_false,
      a03LeadingTensorRawKernel,a03LeadingDualTensorRawKernel,a03LeadingLinearTensorRawKernel,a03LeadingLinearDualTensorRawKernel]
    all_goals dsimp only [p,phaseActualNearTensorData] at *; ring
  rw [he,norm_mul,norm_mul]
  calc
    _≤(1*(D/Real.sqrt (∏ i : Fin 4,a03ZeroModePhysicalQuad qs w x i)))*
        ((C*T^ε)*(204800*T^(2*s-1))) := by
      apply mul_le_mul
      · exact mul_le_mul (a03TensorLogCutoff_norm_le_one _) hden (norm_nonneg _) (by norm_num)
      · exact hffb
      · exact norm_nonneg _
      · positivity
    _=_ := by
      rw [one_mul,show D/Real.sqrt (∏ i : Fin 4,a03ZeroModePhysicalQuad qs w x i)*((C*T^ε)*(204800*T^(2*s-1)))=
        (204800*C*D)*(T^(2*s-1)*T^ε)/Real.sqrt (∏ i : Fin 4,a03ZeroModePhysicalQuad qs w x i) by ring,←Real.rpow_add hT]


theorem a03_zero_linearization_unsorted_native_zero_uniform_mass_bound
    {a b s : ℝ} (hs : s<1) (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ α : MomentShifts,(∀ j,‖α j‖≤1/4) → (∀ j,‖α j‖≤R/Real.log T) → ∀ A B H : ℝ,0<A → 0<B → 0<H → ∀ k : Fin 4→ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+η)) → k 1≠0 → k 3≠0 →
      phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual positive : Bool,
      let p := phaseActualNearTensorData T σ α v A B H k positive
      ‖(T:ℂ)*a03SourceMellinScaleFactor c v α k*
        a03EndpointPhysicalUnsortedZeroMode (a03ZeroModeLinearizationKernel dual Φ c p) T A B H f g k‖≤
        C*T^(2*s+ε)*a03ZeroModeLiteralMass (phaseActualScales A B H k) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨C,hC,hbnd⟩ := a03_zero_linearization_unsorted_kernel_uniform_physical_density hs f g hΦ hΦs hc hc1 hε hκ hθ hR
  refine ⟨F*G*C,by positivity,?_⟩
  filter_upwards [hbnd,eventually_gt_atTop (0:ℝ)] with T hbnd hT
  intro σ hσ hroot α hα hαnorm A B H hA hB hH k hk hk1 hk3 hactive v hv dual positive
  dsimp only
  let p := phaseActualNearTensorData T σ α v A B H k positive
  let q := phaseActualScales A B H k
  let m := false
  let n := false
  let qs := q
  have hqM₁ : 0<q.M₁ := boundaryActual_scale_pos _
  have hqM₂ : 0<q.M₂ := boundaryActual_scale_pos _
  have hM₂ : 0<qs.M₂ := hqM₂
  have hbound := a03SixTensorPhysicalZeroMode_norm_le_literal_mass
    (a03ZeroModeCutoffLinearizationKernel dual Φ c p) (a03SourceMellinScaleFactor c v α k) m n qs hM₂
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
    hF hG (show 0≤C*T^(2*s-1+ε) by positivity)
    (fun u hu => phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt T A f hF hfb hu)
    (fun w hw => phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt T B g hG hgb hw)
    (hbnd σ hσ hroot α hα hαnorm A B H hA hB hH k hk hk1 hk3 hactive v hv dual positive)
  have he : a03SixTensorPhysicalZeroMode (a03ZeroModeCutoffLinearizationKernel dual Φ c p) m n qs
      (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)=
      a03SixTensorPhysicalZeroMode (a03ZeroModeLinearizationKernel dual Φ c p) m n qs
      (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B) := by
    apply a03SixTensorPhysicalZeroMode_congr_on_dyadic_box _ _ m n qs hB _ _
      (phaseActualAmplifierCoefficient_support T g hB)
    intro x hx
    unfold a03ZeroModeCutoffLinearizationKernel
    rw [a03TensorLogCutoff_logPoint_one hx,one_mul]
  rw [he] at hbound
  rw [mul_assoc,norm_mul,Complex.norm_real,Real.norm_of_nonneg hT.le]
  change T*‖a03SourceMellinScaleFactor c v α k*
    a03SixTensorPhysicalZeroMode (a03ZeroModeLinearizationKernel dual Φ c p) m n qs
      (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)‖≤_
  calc
    _≤T*(F*G*(C*T^(2*s-1+ε))*a03ZeroModeLiteralMass qs) := mul_le_mul_of_nonneg_left hbound hT.le
    _=(F*G*C)*T^(2*s+ε)*a03ZeroModeLiteralMass qs := by
      rw [show T*(F*G*(C*T^(2*s-1+ε))*a03ZeroModeLiteralMass qs)=
        (F*G*C)*(T^(1:ℝ)*T^(2*s-1+ε))*a03ZeroModeLiteralMass qs by rw [Real.rpow_one]; ring,
        ←Real.rpow_add hT]
      congr 2
      ring
    _=_ := rfl

end
end Sechstmoment
