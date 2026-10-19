import Sechstmoment.Numerator.U.Sources.PhysicalAggregate

/-! Separate literal physical Gamma moments and their summed sorted GCD
zero modes. The physical source error is their exact Mellin difference. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory Asymptotics
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03ActualSourceBlockValue (zero dual positive : Bool) (Φ : ℝ→ℂ)
    (c T s v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ)
    (i : (Fin 3→ℕ)×(Fin 4→ℕ)) : ℂ :=
  let A := rectangularAFESmoothScale (i.1 0)
  let B := rectangularAFESmoothScale (i.1 1)
  let H := rectangularAFESmoothScale (i.1 2)
  let α := a03SourceShifts dual T σ
  let F := a03SourceRawKernel dual Φ c
  let p := phaseActualNearTensorData T σ α v A B H i.2 positive
  if phaseActualActiveNearBlock T A B H (T^(s-1)) f g i.2 then
    (T:ℂ)*a03SourceMellinScaleFactor c v α i.2*
      (if zero then a03EndpointPhysicalSortedZeroMode (F p) T A B H f g i.2
        else a03EndpointPhysicalTensorSum F positive T A B H σ α v f g i.2)
  else 0

def a03ActualSourceFiniteValue (zero dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s u v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∑ positive : Bool, ∑ i∈a03ActualSourceBlockGrid (T^a) (T^b)
    (8*T^((a+b)/2+s+u/2)) (T^(2+u)),
      a03ActualSourceBlockValue zero dual positive Φ c T s v σ f g i

def a03ActualSourcePhysicalMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s u θ : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualSourceFiniteValue false dual Φ c T a b s u v σ f g

def a03ActualSourceGammaZeroMoment (dual : Bool) (Φ : ℝ→ℂ)
    (c T a b s u θ : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) : ℂ :=
  ∫ v in Icc (-θ*Real.log T) (θ*Real.log T),
    a03ActualSourceFiniteValue true dual Φ c T a b s u v σ f g

theorem a03ActualSourceFiniteError_eq_raw_difference {T : ℝ} (hT : 0<T)
    (dual : Bool) (Φ : ℝ→ℂ) (c e a b s u v : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ) :
    a03ActualSourceFiniteError dual Φ c e T a b s u v σ f g=
      a03ActualSourceFiniteValue false dual Φ c T a b s u v σ f g-
        a03ActualSourceFiniteValue true dual Φ c T a b s u v σ f g := by
  unfold a03ActualSourceFiniteError a03ActualSourceFiniteValue
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro positive _
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [a03ActualSourceBlockError_eq_raw hT]
  unfold a03ActualSourceBlockValue
  dsimp only
  simp only [Bool.false_eq_true,ite_false,ite_true]
  split_ifs <;> ring

theorem a03ActualSourceErrorMoment_eq_physical_sub_zero {T : ℝ} (hT : 0<T)
    (dual : Bool) (Φ : ℝ→ℂ) (c e a b s u θ : ℝ) (σ : MomentShifts) (f g : ℝ→ℝ)
    (hphysical : IntegrableOn (fun v => a03ActualSourceFiniteValue false dual Φ c T a b s u v σ f g)
      (Icc (-θ*Real.log T) (θ*Real.log T)))
    (hzero : IntegrableOn (fun v => a03ActualSourceFiniteValue true dual Φ c T a b s u v σ f g)
      (Icc (-θ*Real.log T) (θ*Real.log T))) :
    a03ActualSourceErrorMoment dual Φ c e T a b s u θ σ f g=
      a03ActualSourcePhysicalMoment dual Φ c T a b s u θ σ f g-
        a03ActualSourceGammaZeroMoment dual Φ c T a b s u θ σ f g := by
  unfold a03ActualSourceErrorMoment a03ActualSourcePhysicalMoment a03ActualSourceGammaZeroMoment
  simp_rw [a03ActualSourceFiniteError_eq_raw_difference hT]
  exact integral_sub hphysical hzero

end
end Sechstmoment
