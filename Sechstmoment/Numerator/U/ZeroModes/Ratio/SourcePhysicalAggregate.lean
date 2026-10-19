import Sechstmoment.Numerator.U.ZeroModes.Ratio.SourceBudget
import Sechstmoment.Numerator.U.ZeroModes.Ratio.SourceErrorAggregate
import Sechstmoment.Numerator.U.ZeroModes.Ratio.TensorMellinIntegrability

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_ratio_source_restored_block_bound
    {T R c u s ε e C : ℝ} (hT : 0<T) (hlog : 1≤Real.log T) (hR : 0≤R)
    (hc : 0≤c) (hc1 : c≤1) (hC : 0≤C)
    (dual positive : Bool) (Φ : ℝ→ℂ) (σ α : MomentShifts) (hα : ∀ j,‖α j‖≤R/Real.log T)
    (v : ℝ) (f g : ℝ→ℝ) (i : (Fin 3→ℕ)×(Fin 4→ℕ))
    (hk : i.2∈rectangularAFEProductScaleGrid (T^(2+u)))
    (hphysical : a03ActualRatioSourceGoodBlock T s ε f g i →
      let A := rectangularAFESmoothScale (i.1 0)
      let B := rectangularAFESmoothScale (i.1 1)
      let H := rectangularAFESmoothScale (i.1 2)
      let native := phaseActualScales A B H i.2
      let F := a03RatioSourceFamilyKernel dual Φ c e (Real.log (native.M₁/native.M₂)) (Real.log (native.N₁/native.N₂))
      let p := phaseActualNearTensorData T σ α v A B H i.2 positive
      ‖a03EndpointPhysicalTensorSum F positive T A B H σ α v f g i.2-
        a03EndpointPhysicalUnsortedZeroMode (F p) T A B H f g i.2‖≤
      C/Real.sqrt (A*B)*phaseSourceMajorant ε (a03SoftSourceOrientedScales
        (boundaryEmbeddedScales (boundaryActualFlags i.2) native))) :
    ‖a03ActualRatioSourceBlockError dual positive Φ c e T s ε v σ α f g i‖≤
      (C*a03SourceMellinBound R u)*T^e*a03ActualSoftSourceBlockMajorant T s ε f g i := by
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  have hA : 0<A := boundaryActual_scale_pos (i.1 0)
  have hB : 0<B := boundaryActual_scale_pos (i.1 1)
  have hm : ‖a03SourceMellinScaleFactor c v α i.2‖≤
      a03SourceMellinBound R u/Real.sqrt ((phaseActualScales A B H i.2).M*(phaseActualScales A B H i.2).N) := by
    simpa [a03SourceMellinBound,phaseActualScales,QuadraticScales.M,QuadraticScales.N] using
      a03SourceMellinScaleFactor_norm_le_of_shifts hT hlog hR hc hc1 α hα i.2 hk v
  by_cases hgood : a03ActualRatioSourceGoodBlock T s ε f g i
  · have hnear := hgood.1
    unfold a03ActualRatioSourceBlockError a03ActualSoftSourceBlockMajorant
    dsimp only
    simp only [hgood,ite_true,hnear]
    have hp := hphysical hgood
    dsimp only at hp
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hT.le,
      Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hT.le e)]
    calc
      _≤(T*(a03SourceMellinBound R u/Real.sqrt ((phaseActualScales A B H i.2).M*(phaseActualScales A B H i.2).N))*T^e)*
        (C/Real.sqrt (A*B)*phaseSourceMajorant ε (a03SoftSourceOrientedScales
          (boundaryEmbeddedScales (boundaryActualFlags i.2) (phaseActualScales A B H i.2)))) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hT.le)
                (Real.rpow_nonneg hT.le e)
            · exact hp
            · exact norm_nonneg _
            · dsimp [a03SourceMellinBound]; positivity
      _=_ := by dsimp [A,B,H]; simp only [Real.sqrt_eq_rpow]; ring
  · unfold a03ActualRatioSourceBlockError
    dsimp only
    simp only [hgood,ite_false,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (by dsimp [a03SourceMellinBound]; positivity))
      (Real.rpow_nonneg hT.le e)) (a03ActualSoftSourceBlockMajorant_nonneg hT.le s ε f g i)

theorem a03_actual_ratio_source_error_moment_bound
    {T a b s u ε e θ C : ℝ} (hT : 1≤T) (hθ : 0≤θ)
    (dual : Bool) (Φ : ℝ→ℂ) (c : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (hblock : ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
      ∀ i∈a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)),
        ‖a03ActualRatioSourceBlockError dual positive Φ c e T s ε v σ α f g i‖≤
          C*T^e*a03ActualSoftSourceBlockMajorant T s ε f g i) :
    ‖a03ActualRatioSourceErrorMoment dual Φ c e T a b s u ε θ σ α f g‖≤
      C*T^e*a03ActualSoftSourceGlobalMajorant T a b s u ε θ f g := by
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  have hfinite (v : ℝ) (hv : |v|≤θ*Real.log T) :
      ‖a03ActualRatioSourceFiniteError dual Φ c e T a b s u ε v σ α f g‖≤
        2*(C*T^e*a03ActualSoftSourceFiniteMajorant T a b s u ε f g) := by
    unfold a03ActualRatioSourceFiniteError
    calc
      _≤∑ positive : Bool, ‖∑ i∈grid,a03ActualRatioSourceBlockError dual positive Φ c e T s ε v σ α f g i‖ :=
        norm_sum_le _ _
      _≤∑ _positive : Bool, C*T^e*a03ActualSoftSourceFiniteMajorant T a b s u ε f g := by
        apply Finset.sum_le_sum
        intro positive _
        calc
          _≤∑ i∈grid, ‖a03ActualRatioSourceBlockError dual positive Φ c e T s ε v σ α f g i‖ := norm_sum_le _ _
          _≤∑ i∈grid,C*T^e*a03ActualSoftSourceBlockMajorant T s ε f g i :=
            Finset.sum_le_sum (hblock v hv positive)
          _=_ := by simp only [a03ActualSoftSourceFiniteMajorant,grid,Finset.mul_sum]
      _=_ := by simp [two_mul]
  have hb := norm_setIntegral_le_of_norm_le_const_ae'
    (measure_Icc_lt_top : volume (Icc (-θ*Real.log T) (θ*Real.log T))<⊤)
    (ae_of_all volume fun v hv => hfinite v (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)))
  unfold a03ActualRatioSourceErrorMoment
  apply hb.trans_eq
  rw [Real.volume_real_Icc,max_eq_left (by nlinarith [Real.log_nonneg hT])]
  unfold a03ActualSoftSourceGlobalMajorant
  ring

/-- Uniform sublinear bound for the literal restored weighted source errors,
including all seven scale sums, both signs, and the Mellin integration. -/
theorem a03_actual_ratio_source_physical_error_aggregate (dual : Bool)
    (hinput : SeparatedQuadraticInput) {a b εsource e c κ θ R : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hεsource : 0<εsource)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (hc : 0<c) (hc1 : c≤1) (he : 12*c<e)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R)
    (hloss : 4*εsource+e<rectangularSlack a b) :
    ∃ s u C : ℝ,0<s ∧ s<1/2 ∧ s≤1/8 ∧ 0<u ∧ u≤1/8 ∧
      s/2+4*εsource+e≤rectangularSlack a b ∧
      3*s/4+u/4+4*εsource+e≤rectangularSlack a b ∧ 0≤C ∧
      (∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ‖a03ActualRatioSourceErrorMoment dual Φ c e T a b s u εsource θ σ α f g‖≤
          C*T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g) ∧
      ∀ δ : ℝ,0<δ → ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
        (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
        ‖a03ActualRatioSourceErrorMoment dual Φ c e T a b s u εsource θ σ α f g‖≤δ*T := by
  obtain ⟨s,u,C,hs,hs2,hscap,hu,hucap,hloss1,hloss2,hC,hphysical⟩ :=
    a03_actual_ratio_tensor_soft_source_physical_bound dual hinput ha hab hlen hεsource
      f g hf hg hΦ hΦs hc hc1 he hκ hθ hR hloss
  let D := C*a03SourceMellinBound R u
  have hD : 0≤D := by dsimp [D,a03SourceMellinBound]; positivity
  have hbound : ∀ᶠ T : ℝ in atTop,∀ σ α : MomentShifts,(∀ j,‖σ j‖≤R) →
      (∀ j,‖α j‖≤R/Real.log T) → (∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖) →
      ‖a03ActualRatioSourceErrorMoment dual Φ c e T a b s u εsource θ σ α f g‖≤
        D*T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g := by
    filter_upwards [hphysical,eventually_ge_atTop (1:ℝ),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
      Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4*R))] with T hphysical hT hlog hlogR
    intro σ α hσ hα hroot
    have hL : 0<Real.log T := zero_lt_one.trans_le hlog
    have hαsmall : ∀ j,‖α j‖≤1/4 := fun j =>
      (hα j).trans ((div_le_iff₀ hL).mpr (by linarith))
    apply a03_actual_ratio_source_error_moment_bound hT hθ dual Φ c σ α f g
    intro v hv positive i hi
    have hk := (Finset.mem_product.mp hi).2
    apply a03_actual_ratio_source_restored_block_bound (zero_lt_one.trans_le hT) hlog hR hc.le hc1 hC
      dual positive Φ σ α hα v f g i hk
    intro hgood
    rcases hgood with ⟨hactive,hmsoft,hnsoft,hk1,hk3⟩
    exact hphysical _ _ _ (boundaryActual_scale_ge_two_thirds (i.1 0))
      (boundaryActual_scale_ge_two_thirds (i.1 1)) (boundaryActual_scale_ge_two_thirds (i.1 2))
      i.2 hk hactive hmsoft hnsoft hk1 hk3 σ α hσ hαsmall hroot v hv positive _ _
  refine ⟨s,u,D,hs,hs2,hscap,hu,hucap,hloss1,hloss2,hD,hbound,?_⟩
  intro δ hδ
  have hsmall := (a03_actual_soft_source_restored_global_majorant_isLittleO
    ha hab hlen hs.le hscap hu hucap hεsource.le hθ hloss1 hloss2 f g hf hg).const_mul_left D
  filter_upwards [hbound,isLittleO_iff.mp hsmall hδ,eventually_ge_atTop (1:ℝ)] with T hb hδb hT
  intro σ α hσ hα hroot
  calc
    _≤D*T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g := hb σ α hσ hα hroot
    _≤‖D*(T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g)‖ := by
      rw [Real.norm_eq_abs]
      simpa only [mul_assoc] using le_abs_self (D*(T^e*a03ActualSoftSourceGlobalMajorant T a b s u εsource θ f g))
    _≤δ*T := by simpa only [Real.norm_of_nonneg (zero_le_one.trans hT)] using hδb

end
end Sechstmoment
