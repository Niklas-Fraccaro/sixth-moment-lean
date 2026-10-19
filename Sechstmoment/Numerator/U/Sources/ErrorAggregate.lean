import Sechstmoment.Numerator.U.Sources.GlobalBudget
import Sechstmoment.Numerator.U.Sources.GlobalMellin
import Sechstmoment.Numerator.U.ZeroModes.SixTensorZeroMode

/-! Literal restored physical source errors, summed on the genuine finite
three-plus-four scale grid and over both signs and the Mellin interval. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03SourceKernel (dual : Bool) (Φ : ℝ→ℂ) (c ε : ℝ) :
    A03NearTensorData→A03SixTensorSpace→ℂ :=
  if dual then a03ActualDualTensorNormalizedKernel Φ c ε
  else a03ActualTensorNormalizedKernel Φ c ε

def a03SourceShifts (dual : Bool) (T : ℝ) (σ : MomentShifts) : MomentShifts :=
  if dual then bblrSixShifts (rawMomentShifts T σ) 1 else rawMomentShifts T σ

def a03SourceRawKernel (dual : Bool) (Φ : ℝ→ℂ) (c : ℝ) :
    A03NearTensorData→A03SixTensorSpace→ℂ :=
  if dual then a03ActualDualTensorRawKernel Φ c else a03ActualTensorRawKernel Φ c

theorem a03EndpointPhysicalTensorSum_const_mul (z : ℂ)
    (F : A03NearTensorData→A03SixTensorSpace→ℂ) (positive : Bool)
    (T A B H : ℝ) (σ α : MomentShifts) (v : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ) :
    a03EndpointPhysicalTensorSum (fun p y => z*F p y) positive T A B H σ α v f g k=
      z*a03EndpointPhysicalTensorSum F positive T A B H σ α v f g k := by
  unfold a03EndpointPhysicalTensorSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem a03EndpointPhysicalSortedZeroMode_const_mul (z : ℂ)
    (F : A03SixTensorSpace→ℂ) (T A B H : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ) :
    a03EndpointPhysicalSortedZeroMode (fun y => z*F y) T A B H f g k=
      z*a03EndpointPhysicalSortedZeroMode F T A B H f g k := by
  unfold a03EndpointPhysicalSortedZeroMode a03SixTensorPhysicalZeroMode
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have hlin (W G : ℝ→ℂ) : (∫ x in Ioi (0:ℝ),W x*(z*G x))=
      z*∫ x in Ioi (0:ℝ),W x*G x := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  rw [hlin]
  ring

theorem a03SourceKernel_phase_eq_raw (dual : Bool) (Φ : ℝ→ℂ)
    (c e T A B H v : ℝ) (σ α : MomentShifts) (k : Fin 4→ℕ) (positive : Bool) :
    a03SourceKernel dual Φ c e (phaseActualNearTensorData T σ α v A B H k positive)=
      fun y => ((T^(-e):ℝ):ℂ)*a03SourceRawKernel dual Φ c
        (phaseActualNearTensorData T σ α v A B H k positive) y := by
  cases dual <;> rfl

def a03ActualSourceBlockError (dual positive : Bool) (Φ : ℝ→ℂ)
    (c εkernel T s v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let α := a03SourceShifts dual T σ
  let F := a03SourceKernel dual Φ c εkernel
  let p := phaseActualNearTensorData T σ α v A B H i.2 positive
  if phaseActualActiveNearBlock T A B H (T^(s-1)) f g i.2 then
    (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*((T^εkernel:ℝ):ℂ)*
      (a03EndpointPhysicalTensorSum F positive T A B H σ α v f g i.2-
        a03EndpointPhysicalSortedZeroMode (F p) T A B H f g i.2)
  else 0

def a03ActualSourceFiniteError (dual : Bool) (Φ : ℝ→ℂ)
    (c εkernel T a b s u v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool, ∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+u/2)) (T^(2+u)),
      a03ActualSourceBlockError dual positive Φ c εkernel T s v σ f g i

def a03ActualSourceErrorMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c εkernel T a b s u θ : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualSourceFiniteError dual Φ c εkernel T a b s u v σ f g

/-- The displayed restored block is exactly the raw Gamma physical sum
minus its raw physical GCD zero mode, with the literal AFE scale factor. -/
theorem a03ActualSourceBlockError_eq_raw {T : ℝ} (hT : 0<T)
    (dual positive : Bool) (Φ : ℝ→ℂ) (c e s v : ℝ) (σ : MomentShifts)
    (f g : ℝ→ℝ) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
    a03ActualSourceBlockError dual positive Φ c e T s v σ f g i=
    let A := rectangularAFESmoothScale (i.1 0)
    let B := rectangularAFESmoothScale (i.1 1)
    let H := rectangularAFESmoothScale (i.1 2)
    let α := a03SourceShifts dual T σ
    let F := a03SourceRawKernel dual Φ c
    let p := phaseActualNearTensorData T σ α v A B H i.2 positive
    if phaseActualActiveNearBlock T A B H (T^(s-1)) f g i.2 then
      (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*
        (a03EndpointPhysicalTensorSum F positive T A B H σ α v f g i.2-
          a03EndpointPhysicalSortedZeroMode (F p) T A B H f g i.2)
    else 0 := by
  unfold a03ActualSourceBlockError
  dsimp only
  split_ifs
  · have hsum : a03EndpointPhysicalTensorSum (a03SourceKernel dual Φ c e) positive T
        (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) σ (a03SourceShifts dual T σ) v f g i.2=
      ((T^(-e):ℝ):ℂ)*a03EndpointPhysicalTensorSum (a03SourceRawKernel dual Φ c) positive T
        (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) σ (a03SourceShifts dual T σ) v f g i.2 := by
      unfold a03EndpointPhysicalTensorSum
      simp_rw [a03SourceKernel_phase_eq_raw]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> ring
    rw [hsum,a03SourceKernel_phase_eq_raw,a03EndpointPhysicalSortedZeroMode_const_mul]
    have hp : ((T^e:ℝ):ℂ)*((T^(-e):ℝ):ℂ)=1 := by
      rw [←Complex.ofReal_mul,←Real.rpow_add hT,add_neg_cancel,Real.rpow_zero,Complex.ofReal_one]
    have halg (X Y Z : ℂ) : X*((T^e:ℝ):ℂ)*(((T^(-e):ℝ):ℂ)*Y-((T^(-e):ℝ):ℂ)*Z)=
        X*(((T^e:ℝ):ℂ)*((T^(-e):ℝ):ℂ))*(Y-Z) := by ring
    rw [halg,hp,mul_one]
  · rfl

def a03SourceMellinBound (R u : ℝ) : ℝ :=
  (((3/2:ℝ)^(3/2+R))^4*Real.exp (R*(Real.log ((3/2:ℝ)^4)+(2+u))))

theorem a03_actual_source_restored_block_bound
    {T R c u s ε e C : ℝ} (hT : 0<T) (hlog : 1≤Real.log T) (hR : 0≤R)
    (hc : 0≤c) (hc1 : c≤1) (_hC : 0≤C)
    (dual positive : Bool) (Φ : ℝ→ℂ) (σ : MomentShifts) (hσ : ∀ j,‖σ j‖≤R)
    (v : ℝ) (f g : ℝ→ℝ) (i : (Fin 3→ℕ)×(Fin 4→ℕ))
    (hk : i.2∈rectangularAFEProductScaleGrid (T^(2+u)))
    (hphysical : phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
      (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2 →
      let A := rectangularAFESmoothScale (i.1 0)
      let B := rectangularAFESmoothScale (i.1 1)
      let H := rectangularAFESmoothScale (i.1 2)
      let α := a03SourceShifts dual T σ
      let F := a03SourceKernel dual Φ c e
      let p := phaseActualNearTensorData T σ α v A B H i.2 positive
      ‖a03EndpointPhysicalTensorSum F positive T A B H σ α v f g i.2-
        a03EndpointPhysicalSortedZeroMode (F p) T A B H f g i.2‖≤
      C/Real.sqrt (A*B)*phaseSourceMajorant ε (phaseNormalizedScales
        (boundaryEmbeddedScales (boundaryActualFlags i.2) (phaseActualScales A B H i.2)))) :
    ‖a03ActualSourceBlockError dual positive Φ c e T s v σ f g i‖≤
      (C*a03SourceMellinBound R u)*T^e*a03ActualSourceBlockMajorant T s ε f g i := by
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  have hA : 0<A := boundaryActual_scale_pos (i.1 0)
  have hB : 0<B := boundaryActual_scale_pos (i.1 1)
  have hm : ‖a03SourceMellinScaleFactor c v (a03SourceShifts dual T σ) i.2‖≤
      a03SourceMellinBound R u/Real.sqrt ((phaseActualScales A B H i.2).M*(phaseActualScales A B H i.2).N) := by
    cases dual
    · simpa [a03SourceShifts,bblrSixShifts,a03SourceMellinBound,phaseActualScales,QuadraticScales.M,QuadraticScales.N] using
        a03SourceMellinScaleFactor_raw_norm_le hT hlog hR hc hc1 σ hσ (0:Fin 6) i.2 hk v
    · simpa [a03SourceShifts,a03SourceMellinBound,phaseActualScales,QuadraticScales.M,QuadraticScales.N] using
        a03SourceMellinScaleFactor_raw_norm_le hT hlog hR hc hc1 σ hσ (1:Fin 6) i.2 hk v
  unfold a03ActualSourceBlockError a03ActualSourceBlockMajorant
  dsimp only
  split_ifs with hactive
  · have hp := hphysical hactive
    dsimp only at hp
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg hT.le,
      Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hT.le e)]
    calc
      _≤(T*(a03SourceMellinBound R u/Real.sqrt ((phaseActualScales A B H i.2).M*(phaseActualScales A B H i.2).N))*T^e)*
        (C/Real.sqrt (A*B)*phaseSourceMajorant ε (phaseNormalizedScales
          (boundaryEmbeddedScales (boundaryActualFlags i.2) (phaseActualScales A B H i.2)))) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hT.le)
                (Real.rpow_nonneg hT.le e)
            · exact hp
            · exact norm_nonneg _
            · dsimp [a03SourceMellinBound]; positivity
      _=_ := by dsimp [A,B,H]; simp only [Real.sqrt_eq_rpow]; ring
  · simp

/-- The additional power restoring the actual Gamma tensor is kept in the
global budget, rather than lost by its normalization. -/
theorem a03_actual_source_restored_global_majorant_isLittleO {a b s u ε e θ : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs0 : 0≤s) (hs : s≤1/8)
    (hu0 : 0<u) (hu : u≤1/8) (hε : 0≤ε) (hθ : 0≤θ)
    (hloss1 : s/2+4*ε+e≤rectangularSlack a b)
    (hloss2 : 3*s/4+u/4+4*ε+e≤rectangularSlack a b)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    (fun T : ℝ => T^e*a03ActualSourceGlobalMajorant T a b s u ε θ f g)=o[atTop]
      (fun T : ℝ => T) := by
  obtain ⟨C,hC,hb⟩ := a03_actual_source_global_majorant_bound ha hab hlen hs0 hs hu0 hu hε hθ f g hf hg
  have henvelope := (polylog_weighted_power_sum_isLittleO hab hlen 8).const_mul_left (256*C)
  apply (show (fun T : ℝ => T^e*a03ActualSourceGlobalMajorant T a b s u ε θ f g)=O[atTop]
    (fun T : ℝ => (256*C)*((Real.log T)^8*(T^rectangularFirstExponent a b (rectangularSlack a b)+
      T^rectangularSecondExponent a b (rectangularSlack a b)))) from ?_).trans_isLittleO henvelope
  apply Eventually.isBigO
  filter_upwards [hb,Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    eventually_ge_atTop (1:ℝ)] with T hb hlog hT
  have hTp : 0<T := zero_lt_one.trans_le hT
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hTp.le e) hb.1)]
  have hl : (1+Real.log T)^8≤256*(Real.log T)^8 := by
    have he := pow_le_pow_left₀ (by linarith : 0≤1+Real.log T) (by linarith : 1+Real.log T≤2*Real.log T) 8
    simpa only [mul_pow,show (2:ℝ)^8=256 by norm_num] using he
  have hp1 : T^(1/2+a+b+s/2+4*ε+e)≤T^rectangularFirstExponent a b (rectangularSlack a b) :=
    Real.rpow_le_rpow_of_exponent_le hT (by unfold rectangularFirstExponent; linarith only [hloss1])
  have hp2 : T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε+e)≤T^rectangularSecondExponent a b (rectangularSlack a b) :=
    Real.rpow_le_rpow_of_exponent_le hT (by unfold rectangularSecondExponent; linarith only [hloss2])
  calc
    _≤T^e*(C*(1+Real.log T)^8*(T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε))) :=
      mul_le_mul_of_nonneg_left hb.2 (Real.rpow_nonneg hTp.le e)
    _=C*(1+Real.log T)^8*(T^(1/2+a+b+s/2+4*ε+e)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε+e)) := by
      simp_rw [Real.rpow_add hTp]
      ring
    _≤C*(256*(Real.log T)^8)*(T^rectangularFirstExponent a b (rectangularSlack a b)+
      T^rectangularSecondExponent a b (rectangularSlack a b)) := by gcongr
    _=_ := by ring

/-- Pointwise estimates of the actual restored physical blocks sum and
integrate with the proved literal majorant; this lemma introduces no mass
or cardinality input. -/
theorem a03_actual_source_error_moment_bound
    {T a b s u ε e θ C : ℝ} (hT : 1≤T) (hθ : 0≤θ)
    (dual : Bool) (Φ : ℝ→ℂ) (c : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ)
    (hblock : ∀ v : ℝ, |v|≤θ*Real.log T → ∀ positive : Bool,
      ∀ i∈a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u)),
        ‖a03ActualSourceBlockError dual positive Φ c e T s v σ f g i‖≤
          C*T^e*a03ActualSourceBlockMajorant T s ε f g i) :
    ‖a03ActualSourceErrorMoment dual Φ c e T a b s u θ σ f g‖≤
      C*T^e*a03ActualSourceGlobalMajorant T a b s u ε θ f g := by
  let grid := a03ActualSourceBlockGrid (T^a) (T^b) (8*T^((a+b)/2+s+u/2)) (T^(2+u))
  have hfinite (v : ℝ) (hv : |v|≤θ*Real.log T) :
      ‖a03ActualSourceFiniteError dual Φ c e T a b s u v σ f g‖≤
        2*(C*T^e*a03ActualSourceFiniteMajorant T a b s u ε f g) := by
    unfold a03ActualSourceFiniteError
    calc
      _≤∑ positive : Bool, ‖∑ i∈grid,a03ActualSourceBlockError dual positive Φ c e T s v σ f g i‖ :=
        norm_sum_le _ _
      _≤∑ _positive : Bool, C*T^e*a03ActualSourceFiniteMajorant T a b s u ε f g := by
        apply Finset.sum_le_sum
        intro positive _
        calc
          _≤∑ i∈grid, ‖a03ActualSourceBlockError dual positive Φ c e T s v σ f g i‖ := norm_sum_le _ _
          _≤∑ i∈grid,C*T^e*a03ActualSourceBlockMajorant T s ε f g i :=
            Finset.sum_le_sum (hblock v hv positive)
          _=_ := by simp only [a03ActualSourceFiniteMajorant,grid,Finset.mul_sum]
      _=_ := by simp [two_mul]
  have hb := norm_setIntegral_le_of_norm_le_const_ae'
    (measure_Icc_lt_top : volume (Icc (-θ*Real.log T) (θ*Real.log T))<⊤)
    (ae_of_all volume fun v hv => hfinite v (abs_le.mpr (by simpa only [mem_Icc,neg_mul] using hv)))
  unfold a03ActualSourceErrorMoment
  apply hb.trans_eq
  rw [Real.volume_real_Icc,max_eq_left (by nlinarith [Real.log_nonneg hT])]
  unfold a03ActualSourceGlobalMajorant
  ring

end
end Sechstmoment
