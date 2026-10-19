import Sechstmoment.Numerator.U.ZeroModes.Ratio.SourceMellin

/-! The literal restored ratio source error on the actual seven-scale grid.
The good mask retains precisely the soft source geometry and native
discrete-unit range; the tensor and native zero are genuine values. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualRatioSourceGoodBlock (T s ε : ℝ) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : Prop :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let q := boundaryEmbeddedScales (boundaryActualFlags i.2) (phaseActualScales A B H i.2)
  phaseActualActiveNearBlock T A B H (T^(s-1)) f g i.2 ∧
    q.M₁≤q.M₂*q.mass^ε ∧ q.N₁≤q.N₂*q.mass^ε ∧ i.2 1≠0 ∧ i.2 3≠0

def a03ActualRatioSourceBlockError (dual positive : Bool) (Φ : ℝ→ℂ)
    (c e T s εsource v : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let native := phaseActualScales A B H i.2
  let F := a03RatioSourceFamilyKernel dual Φ c e (Real.log (native.M₁/native.M₂)) (Real.log (native.N₁/native.N₂))
  let p := phaseActualNearTensorData T σ α v A B H i.2 positive
  if a03ActualRatioSourceGoodBlock T s εsource f g i then
    (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*((T^e:ℝ):ℂ)*
      (a03EndpointPhysicalTensorSum F positive T A B H σ α v f g i.2-
        a03EndpointPhysicalUnsortedZeroMode (F p) T A B H f g i.2)
  else 0

def a03ActualRatioSourceFiniteError (dual : Bool) (Φ : ℝ→ℂ)
    (c e T a b s u εsource v : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool,∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+u/2)) (T^(2+u)),a03ActualRatioSourceBlockError dual positive Φ c e T s εsource v σ α f g i

def a03ActualRatioSourceErrorMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c e T a b s u εsource θ : ℝ) (σ α : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualRatioSourceFiniteError dual Φ c e T a b s u εsource v σ α f g

theorem a03EndpointPhysicalUnsortedZeroMode_const_mul (z : ℂ)
    (F : A03SixTensorSpace→ℂ) (T A B H : ℝ) (f g : ℝ→ℝ) (k : Fin 4→ℕ) :
    a03EndpointPhysicalUnsortedZeroMode (fun y => z*F y) T A B H f g k=
      z*a03EndpointPhysicalUnsortedZeroMode F T A B H f g k := by
  unfold a03EndpointPhysicalUnsortedZeroMode a03SixTensorPhysicalZeroMode
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

theorem a03RatioSourceFamilyKernel_phase_eq_raw {T : ℝ} (hT : 0<T)
    (dual : Bool) (Φ : ℝ→ℂ) (c e tM tN A B H v : ℝ)
    (σ α : MomentShifts) (k : Fin 4→ℕ) (positive : Bool) :
    a03RatioSourceFamilyKernel dual Φ c e tM tN (phaseActualNearTensorData T σ α v A B H k positive)=
      fun y => ((T^(-e):ℝ):ℂ)*a03RatioSourceRawFamilyKernel dual Φ c tM tN
        (phaseActualNearTensorData T σ α v A B H k positive) y := by
  funext y
  exact a03ActualRatioTensorNormalizedKernel_eq hT dual Φ c e _ rfl y

theorem a03ActualRatioSourceBlockError_eq_raw {T : ℝ} (hT : 0<T)
    (dual positive : Bool) (Φ : ℝ→ℂ) (c e s εsource v : ℝ) (σ α : MomentShifts)
    (f g : ℝ→ℝ) (i : (Fin 3→ℕ)×(Fin 4→ℕ)) :
    a03ActualRatioSourceBlockError dual positive Φ c e T s εsource v σ α f g i=
    let A := rectangularAFESmoothScale (i.1 0)
    let B := rectangularAFESmoothScale (i.1 1)
    let H := rectangularAFESmoothScale (i.1 2)
    let native := phaseActualScales A B H i.2
    let F := a03RatioSourceRawFamilyKernel dual Φ c (Real.log (native.M₁/native.M₂)) (Real.log (native.N₁/native.N₂))
    let p := phaseActualNearTensorData T σ α v A B H i.2 positive
    if a03ActualRatioSourceGoodBlock T s εsource f g i then
      (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*
        (a03EndpointPhysicalTensorSum F positive T A B H σ α v f g i.2-
          a03EndpointPhysicalUnsortedZeroMode (F p) T A B H f g i.2)
    else 0 := by
  unfold a03ActualRatioSourceBlockError
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
