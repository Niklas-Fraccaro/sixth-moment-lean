import SixthMoment.Numerator.U.Replacement.GaussianCoefficientGrowth
import SixthMoment.Numerator.U.ZeroModes.Contour.RatioWeight
import SixthMoment.Numerator.U.ZeroModes.PolarChamberInvariance

namespace SixthMoment
open Complex Real Source
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03SourceNormalizedChamber (dual m n : Bool) (σ : MomentShifts) : MomentShifts :=
  a03ZeroModeChamberShifts m n (if dual then bblrSixShifts σ 1 else σ)

def a03ChamberPureRootIndex (dual m n : Bool) (k : PurePolarIndex) : PurePolarIndex :=
  let table : Fin 6→Fin 2→Fin 2→PurePolarIndex :=
    if dual then
      if m then
        if n then
          ![![![(0,(1,1)),(0,(0,1))],![(0,(1,0)),(0,(0,0))]],
      ![![(0,(1,1)),(0,(1,0))],![(0,(0,1)),(0,(0,0))]],
      ![![(0,(1,1)),(2,(1,0))],![(2,(0,1)),(0,(0,0))]],
      ![![(2,(1,0)),(0,(0,1))],![(0,(1,0)),(2,(0,1))]],
      ![![(2,(0,1)),(0,(0,1))],![(0,(1,0)),(2,(1,0))]],
      ![![(0,(1,1)),(2,(0,1))],![(2,(1,0)),(0,(0,0))]]]
        else
          ![![![(0,(0,1)),(0,(1,1))],![(0,(0,0)),(0,(1,0))]],
      ![![(0,(0,1)),(0,(0,0))],![(0,(1,1)),(0,(1,0))]],
      ![![(0,(0,1)),(2,(1,0))],![(2,(0,1)),(0,(1,0))]],
      ![![(2,(1,0)),(0,(1,1))],![(0,(0,0)),(2,(0,1))]],
      ![![(2,(0,1)),(0,(1,1))],![(0,(0,0)),(2,(1,0))]],
      ![![(0,(0,1)),(2,(0,1))],![(2,(1,0)),(0,(1,0))]]]
      else
        if n then
          ![![![(0,(1,0)),(0,(0,0))],![(0,(1,1)),(0,(0,1))]],
      ![![(0,(1,0)),(0,(1,1))],![(0,(0,0)),(0,(0,1))]],
      ![![(0,(1,0)),(2,(1,0))],![(2,(0,1)),(0,(0,1))]],
      ![![(2,(1,0)),(0,(0,0))],![(0,(1,1)),(2,(0,1))]],
      ![![(2,(0,1)),(0,(0,0))],![(0,(1,1)),(2,(1,0))]],
      ![![(0,(1,0)),(2,(0,1))],![(2,(1,0)),(0,(0,1))]]]
        else
          ![![![(0,(0,0)),(0,(1,0))],![(0,(0,1)),(0,(1,1))]],
      ![![(0,(0,0)),(0,(0,1))],![(0,(1,0)),(0,(1,1))]],
      ![![(0,(0,0)),(2,(1,0))],![(2,(0,1)),(0,(1,1))]],
      ![![(2,(1,0)),(0,(1,0))],![(0,(0,1)),(2,(0,1))]],
      ![![(2,(0,1)),(0,(1,0))],![(0,(0,1)),(2,(1,0))]],
      ![![(0,(0,0)),(2,(0,1))],![(2,(1,0)),(0,(1,1))]]]
    else
      if m then
        if n then
          ![![![(0,(1,1)),(0,(1,0))],![(0,(0,1)),(0,(0,0))]],
      ![![(0,(1,1)),(0,(0,1))],![(0,(1,0)),(0,(0,0))]],
      ![![(0,(1,1)),(2,(0,1))],![(2,(1,0)),(0,(0,0))]],
      ![![(2,(0,1)),(0,(1,0))],![(0,(0,1)),(2,(1,0))]],
      ![![(2,(1,0)),(0,(1,0))],![(0,(0,1)),(2,(0,1))]],
      ![![(0,(1,1)),(2,(1,0))],![(2,(0,1)),(0,(0,0))]]]
        else
          ![![![(0,(1,0)),(0,(1,1))],![(0,(0,0)),(0,(0,1))]],
      ![![(0,(1,0)),(0,(0,0))],![(0,(1,1)),(0,(0,1))]],
      ![![(0,(1,0)),(2,(0,1))],![(2,(1,0)),(0,(0,1))]],
      ![![(2,(0,1)),(0,(1,1))],![(0,(0,0)),(2,(1,0))]],
      ![![(2,(1,0)),(0,(1,1))],![(0,(0,0)),(2,(0,1))]],
      ![![(0,(1,0)),(2,(1,0))],![(2,(0,1)),(0,(0,1))]]]
      else
        if n then
          ![![![(0,(0,1)),(0,(0,0))],![(0,(1,1)),(0,(1,0))]],
      ![![(0,(0,1)),(0,(1,1))],![(0,(0,0)),(0,(1,0))]],
      ![![(0,(0,1)),(2,(0,1))],![(2,(1,0)),(0,(1,0))]],
      ![![(2,(0,1)),(0,(0,0))],![(0,(1,1)),(2,(1,0))]],
      ![![(2,(1,0)),(0,(0,0))],![(0,(1,1)),(2,(0,1))]],
      ![![(0,(0,1)),(2,(1,0))],![(2,(0,1)),(0,(1,0))]]]
        else
          ![![![(0,(0,0)),(0,(0,1))],![(0,(1,0)),(0,(1,1))]],
      ![![(0,(0,0)),(0,(1,0))],![(0,(0,1)),(0,(1,1))]],
      ![![(0,(0,0)),(2,(0,1))],![(2,(1,0)),(0,(1,1))]],
      ![![(2,(0,1)),(0,(0,1))],![(0,(1,0)),(2,(1,0))]],
      ![![(2,(1,0)),(0,(0,1))],![(0,(1,0)),(2,(0,1))]],
      ![![(0,(0,0)),(2,(1,0))],![(2,(0,1)),(0,(1,1))]]]
  table k.1 k.2.1 k.2.2

theorem a03NormalizedPureRoot_chamber_square (dual m n : Bool) (σ : MomentShifts)
    (k : PurePolarIndex) :
    (normalizedPurePolarRoot (a03SourceNormalizedChamber dual m n σ) k)^2=
      (normalizedPurePolarRoot σ (a03ChamberPureRootIndex dual m n k))^2 := by
  rcases k with ⟨j,i,l⟩
  cases dual <;> cases m <;> cases n <;> fin_cases j <;> fin_cases i <;> fin_cases l
  all_goals
    norm_num [a03SourceNormalizedChamber,a03ChamberPureRootIndex,normalizedPurePolarRoot,
      purePolarLeft,purePolarRight,bblrSixShifts,a03ZeroModeChamberShifts,a03ZeroModePairPermutation] <;> ring

theorem a03NormalizedPureRoot_chamber_norm (dual m n : Bool) (σ : MomentShifts)
    (k : PurePolarIndex) :
    ‖normalizedPurePolarRoot (a03SourceNormalizedChamber dual m n σ) k‖=
      ‖normalizedPurePolarRoot σ (a03ChamberPureRootIndex dual m n k)‖ := by
  have he := congrArg norm (a03NormalizedPureRoot_chamber_square dual m n σ k)
  simp only [norm_pow] at he
  nlinarith [norm_nonneg (normalizedPurePolarRoot (a03SourceNormalizedChamber dual m n σ) k),
    norm_nonneg (normalizedPurePolarRoot σ (a03ChamberPureRootIndex dual m n k))]

theorem a03NormalizedPureRoot_gap_chambers {κ : ℝ} (σ : MomentShifts)
    (hroot : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (dual m n : Bool) :
    ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot (a03SourceNormalizedChamber dual m n σ) k‖ := by
  intro k
  rw [a03NormalizedPureRoot_chamber_norm]
  exact hroot _

theorem a03SourceNormalizedChamber_raw (dual m n : Bool) (T : ℝ) (σ : MomentShifts) :
    rawMomentShifts T (a03SourceNormalizedChamber dual m n σ)=
      a03ZeroModeChamberShifts m n (if dual then bblrSixShifts (rawMomentShifts T σ) 1
        else rawMomentShifts T σ) := by
  unfold a03SourceNormalizedChamber
  rw [a03_raw_shifts_chamber]
  cases dual
  · rfl
  · simp only [ite_true]
    rw [a03_raw_shifts_six]

end
end SixthMoment
