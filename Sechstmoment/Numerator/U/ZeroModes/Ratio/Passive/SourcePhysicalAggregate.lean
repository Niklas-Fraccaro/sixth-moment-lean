import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.SourceBudget
import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.SourceErrorAggregate
import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.TensorMellinIntegrability

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_passive_ratio_source_restored_block_bound (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop)
    {T R c u s ε e C : ℝ} (hT : 0<T) (hlog : 1≤Real.log T) (hR : 0≤R)
    (hc : 0≤c) (hc1 : c≤1) (hC : 0≤C)
    (dual positive : Bool) (Φ : ℝ→ℂ) (σ α : MomentShifts) (hα : ∀ j,‖α j‖≤R/Real.log T)
    (v : ℝ) (f g : ℝ→ℝ) (i : (Fin 3→ℕ)×(Fin 4→ℕ))
    (hk : i.2∈rectangularAFEProductScaleGrid (T^(2+u)))
    (hphysical : a03ActualPassiveRatioSourceGoodBlock T s ε f g i →
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
    ‖a03ActualPassiveRatioSourceBlockError select dual positive Φ c e T s ε v σ α f g i‖≤
      (C*a03SourceMellinBound R u)*T^e*a03ActualPassiveSoftSourceBlockMajorant T s ε f g i := by
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  have hA : 0<A := boundaryActual_scale_pos (i.1 0)
  have hB : 0<B := boundaryActual_scale_pos (i.1 1)
  have hm : ‖a03SourceMellinScaleFactor c v α i.2‖≤
      a03SourceMellinBound R u/Real.sqrt ((phaseActualScales A B H i.2).M*(phaseActualScales A B H i.2).N) := by
    simpa [a03SourceMellinBound,phaseActualScales,QuadraticScales.M,QuadraticScales.N] using
      a03SourceMellinScaleFactor_norm_le_of_shifts hT hlog hR hc hc1 α hα i.2 hk v
  by_cases hgood : select i ∧ a03ActualPassiveRatioSourceGoodBlock T s ε f g i
  · have hnear := hgood.2.1
    unfold a03ActualPassiveRatioSourceBlockError a03ActualPassiveSoftSourceBlockMajorant
    dsimp only
    rw [ite_eq_left hgood,ite_eq_left hnear]
    have hp := hphysical hgood.2
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
  · unfold a03ActualPassiveRatioSourceBlockError
    dsimp only
    simp only [hgood,ite_false,norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC (by dsimp [a03SourceMellinBound]; positivity))
      (Real.rpow_nonneg hT.le e)) (a03ActualPassiveSoftSourceBlockMajorant_nonneg hT.le s ε f g i)

theorem a03_actual_passive_ratio_source_error_moment_bound (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop)
    {T a b s u ε e θ C : ℝ} (hT : 1≤T) (hθ : 0≤θ)
    (dual : Bool) (Φ : ℝ→ℂ) (c : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (hblock : ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
      ∀ i∈a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)),
        ‖a03ActualPassiveRatioSourceBlockError select dual positive Φ c e T s ε v σ α f g i‖≤
          C*T^e*a03ActualPassiveSoftSourceBlockMajorant T s ε f g i) :
    ‖a03ActualPassiveRatioSourceErrorMoment select dual Φ c e T a b s u ε θ σ α f g‖≤
      C*T^e*a03ActualPassiveSoftSourceGlobalMajorant T a b s u ε θ f g := by
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  have hfinite (v : ℝ) (hv : |v|≤θ*Real.log T) :
      ‖a03ActualPassiveRatioSourceFiniteError select dual Φ c e T a b s u ε v σ α f g‖≤
        2*(C*T^e*a03ActualPassiveSoftSourceFiniteMajorant T a b s u ε f g) := by
    unfold a03ActualPassiveRatioSourceFiniteError
    calc
      _≤∑ positive : Bool, ‖∑ i∈grid,a03ActualPassiveRatioSourceBlockError select dual positive Φ c e T s ε v σ α f g i‖ :=
        norm_sum_le _ _
      _≤∑ _positive : Bool, C*T^e*a03ActualPassiveSoftSourceFiniteMajorant T a b s u ε f g := by
        apply Finset.sum_le_sum
        intro positive _
        calc
          _≤∑ i∈grid, ‖a03ActualPassiveRatioSourceBlockError select dual positive Φ c e T s ε v σ α f g i‖ := norm_sum_le _ _
          _≤∑ i∈grid,C*T^e*a03ActualPassiveSoftSourceBlockMajorant T s ε f g i :=
            Finset.sum_le_sum (hblock v hv positive)
          _=_ := by simp only [a03ActualPassiveSoftSourceFiniteMajorant,grid,Finset.mul_sum]
      _=_ := by simp [two_mul]
  have hb := norm_setIntegral_le_of_norm_le_const_ae'
    (measure_Icc_lt_top : volume (Icc (-θ*Real.log T) (θ*Real.log T))<⊤)
    (ae_of_all volume fun v hv => hfinite v (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)))
  unfold a03ActualPassiveRatioSourceErrorMoment
  apply hb.trans_eq
  rw [Real.volume_real_Icc,max_eq_left (by nlinarith [Real.log_nonneg hT])]
  unfold a03ActualPassiveSoftSourceGlobalMajorant
  ring


end
end Sechstmoment
