import Sechstmoment.Numerator.U.ZeroModes.Ratio.Passive.SourceEndpoint

/-! The literal restored ratio source error on the actual seven-scale grid.
The good mask retains precisely the soft source geometry and native
discrete-unit range; the tensor and native zero are genuine values. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualPassiveRatioSourceGoodBlock (T s ε : ℝ) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : Prop :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let q := boundaryEmbeddedScales (boundaryActualFlags i.2) (phaseActualScales A B H i.2)
  A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g i.2 ∧
    q.M₁≤q.M₂*q.mass^ε ∧ q.N₁≤q.N₂*q.mass^ε ∧ i.2 1≠0 ∧ i.2 3≠0

def a03ActualPassiveRatioSourceSelectedGoodBlock (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop)
    (T s ε : ℝ) (f g : ℝ→ℝ) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : Prop :=
  select i ∧ a03ActualPassiveRatioSourceGoodBlock T s ε f g i

def a03ActualPassiveRatioSourceBlockError (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (dual positive : Bool) (Φ : ℝ→ℂ)
    (c e T s εsource v : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let native := phaseActualScales A B H i.2
  let F := a03RatioSourceFamilyKernel dual Φ c e (Real.log (native.M₁/native.M₂)) (Real.log (native.N₁/native.N₂))
  let p := phaseActualNearTensorData T σ α v A B H i.2 positive
  if select i ∧ a03ActualPassiveRatioSourceGoodBlock T s εsource f g i then
    (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*((T^e:ℝ):ℂ)*
      (a03EndpointPhysicalTensorSum F positive T A B H σ α v f g i.2-
        a03EndpointPhysicalUnsortedZeroMode (F p) T A B H f g i.2)
  else 0

def a03ActualPassiveRatioSourceFiniteError (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (dual : Bool) (Φ : ℝ→ℂ)
    (c e T a b s u εsource v : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool,∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+u/2)) (T^(2+u)),a03ActualPassiveRatioSourceBlockError select dual positive Φ c e T s εsource v σ α f g i

def a03ActualPassiveRatioSourceErrorMoment (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) (dual : Bool) (Φ : ℝ→ℂ)
    (c e T a b s u εsource θ : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualPassiveRatioSourceFiniteError select dual Φ c e T a b s u εsource v σ α f g

theorem a03ActualPassiveRatioSourceBlockError_eq_raw (select : ((Fin 3→ℕ)×(Fin 4→ℕ))→Prop) {T : ℝ} (hT : 0<T)
    (dual positive : Bool) (Φ : ℝ→ℂ) (c e s εsource v : ℝ) (σ α : MomentShifts)
    (f g : ℝ→ℝ) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
    a03ActualPassiveRatioSourceBlockError select dual positive Φ c e T s εsource v σ α f g i=
    let A := rectangularAFESmoothScale (i.1 0)
    let B := rectangularAFESmoothScale (i.1 1)
    let H := rectangularAFESmoothScale (i.1 2)
    let native := phaseActualScales A B H i.2
    let F := a03RatioSourceRawFamilyKernel dual Φ c (Real.log (native.M₁/native.M₂)) (Real.log (native.N₁/native.N₂))
    let p := phaseActualNearTensorData T σ α v A B H i.2 positive
    if select i ∧ a03ActualPassiveRatioSourceGoodBlock T s εsource f g i then
      (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*
        (a03EndpointPhysicalTensorSum F positive T A B H σ α v f g i.2-
          a03EndpointPhysicalUnsortedZeroMode (F p) T A B H f g i.2)
    else 0 := by
  unfold a03ActualPassiveRatioSourceBlockError
  dsimp only
  split_ifs
  · have hsum : ∀ tM tN : ℝ,
      a03EndpointPhysicalTensorSum (a03RatioSourceFamilyKernel dual Φ c e tM tN) positive T
        (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) σ α v f g i.2=
      ((T^(-e):ℝ):ℂ)*a03EndpointPhysicalTensorSum (a03RatioSourceRawFamilyKernel dual Φ c tM tN) positive T
        (rectangularAFESmoothScale (i.1 0)) (rectangularAFESmoothScale (i.1 1))
        (rectangularAFESmoothScale (i.1 2)) σ α v f g i.2 := by
      intro tM tN
      unfold a03EndpointPhysicalTensorSum
      simp_rw [a03RatioSourceFamilyKernel_phase_eq_raw hT]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      split_ifs <;> ring
    rw [hsum,a03RatioSourceFamilyKernel_phase_eq_raw hT,a03EndpointPhysicalUnsortedZeroMode_const_mul]
    have hp : ((T^e:ℝ):ℂ)*((T^(-e):ℝ):ℂ)=1 := by
      rw [←Complex.ofReal_mul,←Real.rpow_add hT,add_neg_cancel,Real.rpow_zero,Complex.ofReal_one]
    have halg (X Y Z : ℂ) : X*((T^e:ℝ):ℂ)*(((T^(-e):ℝ):ℂ)*Y-((T^(-e):ℝ):ℂ)*Z)=
        X*(((T^e:ℝ):ℂ)*((T^(-e):ℝ):ℂ))*(Y-Z) := by ring
    rw [halg,hp,mul_one]
  · rfl

end
end Sechstmoment
