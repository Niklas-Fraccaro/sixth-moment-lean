import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.ArithmeticChamberIdentification

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 300000

def a03BoolPairIndex (b : Bool) : Fin 2 := if b then 1 else 0

def a03ChamberMainPoleIndex (m n : Bool) (j : Fin 2) : PurePolarIndex :=
  (0,(a03BoolPairIndex (if j=0 then m else !m),
    a03BoolPairIndex (if j=0 then n else !n)))

theorem a03ChamberMainPoleRoot_eq (T : ℝ) (m n : Bool) (σ : MomentShifts) (j : Fin 2) :
    a03ZeroModeMainPoleRoot T (a03ZeroModeChamberShifts m n σ) j=
      purePolarRoot T σ (a03ChamberMainPoleIndex m n j) := by
  fin_cases j
  · change a03ZeroModeMainPoleRoot T (a03ZeroModeChamberShifts m n σ) 0=
      purePolarRoot T σ (a03ChamberMainPoleIndex m n 0)
    rw [a03ZeroModeMainPoleRoot_zero,a03_raw_shifts_chamber]
    cases m <;> cases n <;> norm_num [a03ChamberMainPoleIndex,a03BoolPairIndex,purePolarRoot,
      purePolarLeft,purePolarRight,bblrSixShifts,a03ZeroModeChamberShifts,a03ZeroModePairPermutation]
  · change a03ZeroModeMainPoleRoot T (a03ZeroModeChamberShifts m n σ) 1=
      purePolarRoot T σ (a03ChamberMainPoleIndex m n 1)
    rw [a03ZeroModeMainPoleRoot_one,a03_raw_shifts_chamber]
    cases m <;> cases n <;> norm_num [a03ChamberMainPoleIndex,a03BoolPairIndex,purePolarRoot,
      purePolarLeft,purePolarRight,bblrSixShifts,a03ZeroModeChamberShifts,a03ZeroModePairPermutation]

theorem a03ChamberMainContour_initial_pair_eq_crossed {T δ κ : ℝ} (hT : 1<T)
    (hδ : 0<δ) (hδ1 : δ<1/4) (hκ : 0<κ) (m n : Bool) (σ : MomentShifts)
    (hα : ∀ j,‖rawMomentShifts T σ j‖≤δ/4)
    (hroot : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (N₁ N₂ : ℕ) (A B : ℕ→ℂ) :
    a03ZeroModeContourPrefactor (a03ZeroModeChamberShifts m n (rawMomentShifts T σ))*
      (verticalIntegral 1 (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ A B
        (a03ZeroModeChamberShifts m n (rawMomentShifts T σ)))+
      verticalIntegral 1 (a03ZeroModeMainKernel (polarPoleKiller T σ) N₁ N₂ A B
        (a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts (rawMomentShifts T σ) 1))))=
      a03CrossedArithmeticSum N₁ N₂ A B (a03ZeroModeChamberShifts m n (rawMomentShifts T σ)) := by
  have hα' : ∀ j,‖rawMomentShifts T (a03ZeroModeChamberShifts m n σ) j‖≤δ/4 := by
    rw [a03_raw_shifts_chamber]
    intro j
    change ‖rawMomentShifts T σ (a03ZeroModePairPermutation m n j)‖≤δ/4
    exact hα (a03ZeroModePairPermutation m n j)
  have hρ (j : Fin 2) : a03ZeroModeMainPoleRoot T (a03ZeroModeChamberShifts m n σ) j≠0 := by
    rw [a03ChamberMainPoleRoot_eq,purePolarRoot_normalized]
    exact div_ne_zero (norm_pos_iff.mp (hκ.trans_le (hroot (a03ChamberMainPoleIndex m n j))))
      (Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne')
  have he := a03ZeroModeMainContour_initial_pair (a03ZeroModeChamberShifts m n σ)
    N₁ N₂ A B hδ hδ1 hα' hρ
  have hG : polarPoleKiller T (a03ZeroModeChamberShifts m n σ)=polarPoleKiller T σ :=
    funext (a03PolarPoleKiller_chamber T m n σ)
  rw [hG,a03_raw_shifts_chamber,a03ZeroMode_chamber_dual_partner] at he
  rw [he]
  exact a03ZeroModeMainContour_chamber_zero_value m n N₁ N₂ A B
    (fun j => (hα j).trans (by linarith))

def a03ChamberMainPairMoment (m n : Bool) (T a b : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ,(Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^
      (-(a03ZeroModeChamberShifts m n (rawMomentShifts T σ) 1)-
        (a03ZeroModeChamberShifts m n (rawMomentShifts T σ) 3))*
    (a03ZeroModeContourPrefactor (a03ZeroModeChamberShifts m n (rawMomentShifts T σ))*
      (verticalIntegral 1 (a03ZeroModeMainKernel (polarPoleKiller T σ) ⌊T^a⌋₊ ⌊T^b⌋₊
        (fun k : ℕ => (f (Real.log k/Real.log T):ℂ))
        (fun k : ℕ => (g (Real.log k/Real.log T):ℂ))
        (a03ZeroModeChamberShifts m n (rawMomentShifts T σ)))+
      verticalIntegral 1 (a03ZeroModeMainKernel (polarPoleKiller T σ) ⌊T^a⌋₊ ⌊T^b⌋₊
        (fun k : ℕ => (f (Real.log k/Real.log T):ℂ))
        (fun k : ℕ => (g (Real.log k/Real.log T):ℂ))
        (a03ZeroModeChamberShifts (!n) (!m) (bblrSixShifts (rawMomentShifts T σ) 1)))))

theorem a03ChamberMainPairMoment_eventually_eq_indexed (K : Set MomentShifts) (hK : IsCompact K)
    {κ : ℝ} (hκ : 0<κ)
    (hroot : ∀ σ∈K,∀ j : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ j‖)
    (a b : ℝ) (f g Φ : ℝ→ℝ) :
    ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ m n : Bool,
      a03ChamberMainPairMoment m n T a b σ f g Φ=
        a03DiagonalArithmeticIndexedMainTerm (a03CrossedChamberLabel m n)
          T a b (rawMomentShifts T σ) f g Φ := by
  filter_upwards [compactNormalizedShifts_eventually_norm_small K hK (1/32)
    (by norm_num),eventually_gt_atTop (1:ℝ)] with T hsmall hT
  intro σ hσ m n
  have he := a03ChamberMainContour_initial_pair_eq_crossed hT (δ:=1/8)
    (by norm_num) (by norm_num) hκ m n σ
    (by simpa only [show (1/8:ℝ)/4=1/32 by norm_num] using hsmall σ hσ) (hroot σ hσ)
    ⌊T^a⌋₊ ⌊T^b⌋₊ (fun k : ℕ => (f (Real.log k/Real.log T):ℂ))
    (fun k : ℕ => (g (Real.log k/Real.log T):ℂ))
  unfold a03ChamberMainPairMoment
  simp_rw [he]
  exact a03CrossedChamberArithmeticMoment_eq_indexed m n T a b (rawMomentShifts T σ) f g Φ

end
end Sechstmoment
