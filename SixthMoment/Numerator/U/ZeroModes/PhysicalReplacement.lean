import SixthMoment.Numerator.U.Sources.ErrorAggregate
import SixthMoment.Numerator.U.ZeroModes.ActualMass
import SixthMoment.Numerator.U.ZeroModes.PhysicalBound
import SixthMoment.Numerator.U.ZeroModes.Replacement.Kernels

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ZeroModeReplacementKernel (dual : Bool) (Φ : ℝ→ℂ) (c : ℝ) :
    A03NearTensorData→A03SixTensorSpace→ℂ :=
  if dual then a03ReplacementDualTensorRawKernel Φ c else a03ReplacementTensorRawKernel Φ c

def a03ZeroModeLeadingKernel (dual : Bool) (Φ : ℝ→ℂ) (c : ℝ) :
    A03NearTensorData→A03SixTensorSpace→ℂ :=
  if dual then a03LeadingDualTensorRawKernel Φ c else a03LeadingTensorRawKernel Φ c

theorem a03ZeroModePermutedPhysicalQuad_lower (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) (x : ℝ) (hl : ∀ i,1≤a03ZeroModePhysicalQuad q v x i) :
    ∀ i,1≤a03ZeroModePermutedPhysicalQuad m n q v x i := by
  intro i
  cases m <;> cases n <;> fin_cases i <;>
    simp [a03ZeroModePermutedPhysicalQuad] <;>
    first | exact hl 0 | exact hl 1 | exact hl 2 | exact hl 3

private theorem actual_pair_positive (A B H : ℝ) (k : Fin 4→ℕ)
    (hA : 0<A) (hB : 0<B) (hH : 0<H) (m n : Bool) :
    ∀ j,0<(phasePairSwapScales m n (phaseActualScales A B H k)).size j := by
  intro j
  cases m <;> cases n <;> fin_cases j <;>
    simp [phasePairSwapScales,phaseActualScales,QuadraticScales.size] <;>
    first | exact hA | exact hB | exact hH | exact boundaryActual_scale_pos _

theorem a03_zero_replacement_kernel_uniform_physical_density
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ l : Fin 6,∀ A B H : ℝ,0<A → 0<B → 0<H → ∀ k : Fin 4→ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+η)) → (∀ j,k j≠1) →
      ¬(k 0=0 ∧ k 1=0) → ¬(k 2=0 ∧ k 3=0) →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual positive : Bool,
      let α := bblrSixShifts (rawMomentShifts T σ) l
      let p := phaseActualNearTensorData T σ α v A B H k positive
      let q := phaseActualScales A B H k
      let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
      let m := decide (q'.M₂<q'.M₁)
      let n := decide (q'.N₂<q'.N₁)
      let qs := phasePairSwapScales m n q
      ∀ w∈quadraticMainIndexSet qs,∀ x : ℝ,0<x → a03ZeroModeSmoothProduct qs w x≠0 →
        ‖a03SourceMellinScaleFactor c v α k*
          a03ZeroModeReplacementKernel dual Φ c p
            (a03SixTensorLogPoint (a03SixZeroSourceArguments m n qs w x))‖≤
          C*T^(ε-1)/Real.sqrt (∏ i : Fin 4,a03ZeroModePhysicalQuad qs w x i) := by
  obtain ⟨C,hC,hf⟩ := a03ZeroModeReplacementFrequency_uniform_bound hΦ hΦs hc hc1 hε hκ hθ
  obtain ⟨D,hD,hd⟩ := a03_gaussian_dual_replacement_frequency_logarithmic_uniform_derivative_bounds
    hΦ hΦs hc hc1 hε hκ hθ hR
  have hD00 := hD 0 0
  let E := Real.exp (R*(Real.log 16+(2+η)))
  refine ⟨(C+D 0 0)*E,by positivity,?_⟩
  filter_upwards [hf,hd,rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4),
    eventually_gt_atTop (0:ℝ),Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))]
    with T hf hd hsmall hT hlog
  intro σ hσ hroot l A B H hA hB hH k hk hidx hm hn v hv dual positive
  dsimp only
  let α := bblrSixShifts (rawMomentShifts T σ) l
  let q := phaseActualScales A B H k
  let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
  let m := decide (q'.M₂<q'.M₁)
  let n := decide (q'.N₂<q'.N₁)
  let qs := phasePairSwapScales m n q
  have hqs := actual_pair_positive A B H k hA hB hH m n
  have hsmallα := bblrSixShifts_norm_le _ (hsmall σ hσ) l
  have hsizes := a03_actual_sorted_integrated_scales_ge_one A B H k hidx hm hn
  have hcut : qs.M*qs.N≤T^(2+η) := by
    rw [(phase_pair_swap_products m n q).1,(phase_pair_swap_products m n q).2.1]
    simpa [q,phaseActualScales,QuadraticScales.M,QuadraticScales.N,Fin.prod_univ_four,mul_assoc]
      using (Finset.mem_filter.mp hk).2
  intro w hw x hx hω
  have hw1 (j : Fin 5) : 1≤w j := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw j)).1
  have hb := a03ZeroModePhysicalQuad_nonzero_mask_bounds qs hqs hsizes.1 hsizes.2 w hw x hω
  have hperm := a03ZeroModePermutedPhysicalQuad_lower m n qs w x hb.1
  have hpcut : (∏ i : Fin 4,a03ZeroModePermutedPhysicalQuad m n qs w x i)≤16*T^(2+η) := by
    rw [a03ZeroModePermutedPhysicalQuad_product]
    exact hb.2.trans (mul_le_mul_of_nonneg_left hcut (by norm_num))
  have hden := a03ZeroModeRealQuadDenominator_raw_inv_norm_le hT hlog (by norm_num : (1:ℝ)≤16) hR
    σ hσ l ((c:ℂ)+(v:ℂ)*I) (by simpa using hc.le) _ hperm hpcut
  rw [a03ZeroModePermutedPhysicalQuad_product] at hden
  have hfreq (ξ : ℝ) :
      ‖if dual then a03GaussianDualReplacementFrequencyProfile Φ T σ σ α ((c:ℂ)+(v:ℂ)*I) ξ
        else a03GaussianReplacementFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I) ξ‖≤(C+D 0 0)*T^(ε-1) := by
    cases dual
    · simp only [Bool.false_eq_true,ite_false]
      exact (hf σ α hsmallα hroot v hv ξ).trans (by gcongr; exact le_add_of_nonneg_right (hD 0 0))
    · simp only [ite_true]
      have h := hd σ σ α hσ hsmallα hroot v hv 0 0 ξ
      simp only [pow_zero,iteratedDeriv_zero,one_mul] at h
      exact h.trans (by gcongr; exact le_add_of_nonneg_left hC)
  have hscale := a03ZeroModeMellinScaleFactor_pair_actual m n A B H c v α k
  rw [←hscale]
  have he : a03ZeroModeReplacementKernel dual Φ c
      (phaseActualNearTensorData T σ α v A B H k positive)
      (a03SixTensorLogPoint (a03SixZeroSourceArguments m n qs w x))=
      a03TensorMellinFactor α ((c:ℂ)+(v:ℂ)*I)
        (a03SixTensorLogPoint (a03SixZeroSourceArguments m n qs w x))*
      (if dual then a03GaussianDualReplacementFrequencyProfile Φ T σ σ α ((c:ℂ)+(v:ℂ)*I)
        (-a03RealLogGapSymbol T (phaseActualNearTensorData T σ α v A B H k positive).r
          (phaseActualNearTensorData T σ α v A B H k positive).s
          (a03SixGapLinear (a03SixTensorLogPoint (a03SixZeroSourceArguments m n qs w x))))
      else a03GaussianReplacementFrequencyProfile Φ T σ α ((c:ℂ)+(v:ℂ)*I)
        (-a03RealLogGapSymbol T (phaseActualNearTensorData T σ α v A B H k positive).r
          (phaseActualNearTensorData T σ α v A B H k positive).s
          (a03SixGapLinear (a03SixTensorLogPoint (a03SixZeroSourceArguments m n qs w x))))) := by
    cases dual <;> rfl
  rw [he,←mul_assoc,a03ZeroMode_scale_mellin_eq_denominator m n qs hqs α _ w hw1 hx,norm_mul]
  calc
    _≤(E/Real.sqrt (∏ i : Fin 4,a03ZeroModePhysicalQuad qs w x i))*((C+D 0 0)*T^(ε-1)) :=
      mul_le_mul hden (hfreq _) (norm_nonneg _) (by positivity)
    _=_ := by ring


theorem a03_zero_replacement_native_zero_uniform_mass_bound
    {a b : ℝ} (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ R η : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ : MomentShifts,
      (∀ j,‖σ j‖≤R) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ l : Fin 6,∀ A B H : ℝ,0<A → 0<B → 0<H → ∀ k : Fin 4→ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+η)) → (∀ j,k j≠1) →
      ¬(k 0=0 ∧ k 1=0) → ¬(k 2=0 ∧ k 3=0) →
      ∀ v : ℝ,|v|≤θ*Real.log T → ∀ dual positive : Bool,
      let α := bblrSixShifts (rawMomentShifts T σ) l
      let p := phaseActualNearTensorData T σ α v A B H k positive
      ‖(T:ℂ)*a03SourceMellinScaleFactor c v α k*
          a03EndpointPhysicalSortedZeroMode (a03ZeroModeReplacementKernel dual Φ c p) T A B H f g k‖≤
        C*T^ε*a03ZeroModeLiteralMass (a03ActualZeroModeSortedScales A B H k) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨C,hC,hbnd⟩ := a03_zero_replacement_kernel_uniform_physical_density hΦ hΦs hc hc1 hε hκ hθ hR
  refine ⟨F*G*C,by positivity,?_⟩
  filter_upwards [hbnd,eventually_gt_atTop (0:ℝ)] with T hbnd hT
  intro σ hσ hroot l A B H hA hB hH k hk hidx hm hn v hv dual positive
  dsimp only
  let α := bblrSixShifts (rawMomentShifts T σ) l
  let p := phaseActualNearTensorData T σ α v A B H k positive
  let q := phaseActualScales A B H k
  let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
  let m := decide (q'.M₂<q'.M₁)
  let n := decide (q'.N₂<q'.N₁)
  let qs := phasePairSwapScales m n q
  have hp := actual_pair_positive A B H k hA hB hH m n
  have hM₂ : 0<qs.M₂ := by simpa [QuadraticScales.size] using hp 3
  have hbound := a03SixTensorPhysicalZeroMode_norm_le_literal_mass
    (a03ZeroModeReplacementKernel dual Φ c p) (a03SourceMellinScaleFactor c v α k) m n qs hM₂
    (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)
    hF hG (show 0≤C*T^(ε-1) by positivity)
    (fun u hu => phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt T A f hF hfb hu)
    (fun w hw => phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt T B g hG hgb hw)
    (hbnd σ hσ hroot l A B H hA hB hH k hk hidx hm hn v hv dual positive)
  rw [mul_assoc,norm_mul,Complex.norm_real,Real.norm_of_nonneg hT.le]
  change T*‖a03SourceMellinScaleFactor c v α k*
    a03SixTensorPhysicalZeroMode (a03ZeroModeReplacementKernel dual Φ c p) m n qs
      (phaseActualAmplifierCoefficient T f A) (phaseActualAmplifierCoefficient T g B)‖≤_
  calc
    _≤T*(F*G*(C*T^(ε-1))*a03ZeroModeLiteralMass qs) := mul_le_mul_of_nonneg_left hbound hT.le
    _=(F*G*C)*T^ε*a03ZeroModeLiteralMass qs := by
      rw [show T*(F*G*(C*T^(ε-1))*a03ZeroModeLiteralMass qs)=
        (F*G*C)*(T^(1:ℝ)*T^(ε-1))*a03ZeroModeLiteralMass qs by rw [Real.rpow_one]; ring,
        ←Real.rpow_add hT]
      congr 2
      ring
    _=_ := rfl

end
end SixthMoment
