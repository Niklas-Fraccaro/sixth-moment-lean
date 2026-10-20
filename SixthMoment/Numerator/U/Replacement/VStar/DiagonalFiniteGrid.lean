import SixthMoment.Numerator.U.Replacement.VStar.DiagonalMoment

namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def bblrVStarSelectedSmoothProductGrid (diagonal : Bool) (G : ℂ→ℂ) (α : MomentShifts)
    (u w : ℕ) (t X : ℝ) : ℂ :=
  ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
    (rectangularAFESmoothWeight k n:ℂ)*
      (if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true) then bblrVStarAFESummand G α t n else 0)

def bblrVStarSelectedSmoothProductTail (diagonal : Bool) (G : ℂ→ℂ) (α : MomentShifts)
    (u w : ℕ) (t X : ℝ) : ℂ :=
  ∑' n : Fin 4→ℕ, (rectangularAFESmoothTailWeight X n:ℂ)*
    (if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true) then bblrVStarAFESummand G α t n else 0)

def bblrVStarSelectedFiniteCore (diagonal : Bool) (c T : ℝ) (σ α : MomentShifts)
    (u w : ℕ) (t X R : ℝ) : ℂ :=
  ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
    (rectangularAFESmoothWeight k n:ℂ)*
      (if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true) then bblrGaussianVStarCoreSummand c T σ α t R n else 0)

def bblrVStarSelectedGridFrequencyTail (diagonal : Bool) (c T : ℝ) (σ α : MomentShifts)
    (u w : ℕ) (t X R : ℝ) : ℂ :=
  ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
    (rectangularAFESmoothWeight k n:ℂ)*
      (if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true) then
        bblrVStarAFESummand (polarPoleKiller T σ) α t n-bblrGaussianVStarCoreSummand c T σ α t R n else 0)

def bblrVStarSelectedFiniteRemainder (diagonal : Bool) (c T : ℝ) (σ α : MomentShifts)
    (u w : ℕ) (t X R : ℝ) : ℂ :=
  bblrVStarSelectedSmoothProductTail diagonal (polarPoleKiller T σ) α u w t X+
    bblrVStarSelectedGridFrequencyTail diagonal c T σ α u w t X R

def rectangularVStarSelectedFiniteIntegrand (diagonal : Bool) (c T a b : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) (X R t : ℝ) : ℂ :=
  ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    rectangularMomentPairWeight T f g Φ u w t*
      (bblrVStarSelectedFiniteCore diagonal c T σ (rawMomentShifts T σ) u w t X R+
        bblrDualLeadingMultiplier T σ (t/T)*
          bblrVStarSelectedFiniteCore diagonal c T σ (bblrSixShifts (rawMomentShifts T σ) 1) u w t X R)

def rectangularVStarSelectedFiniteRemainderIntegrand (diagonal : Bool) (c T a b : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) (X R t : ℝ) : ℂ :=
  ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    rectangularMomentPairWeight T f g Φ u w t*
      (bblrVStarSelectedFiniteRemainder diagonal c T σ (rawMomentShifts T σ) u w t X R+
        bblrDualLeadingMultiplier T σ (t/T)*
          bblrVStarSelectedFiniteRemainder diagonal c T σ (bblrSixShifts (rawMomentShifts T σ) 1) u w t X R)

def rectangularVStarSelectedFiniteMoment (diagonal : Bool) (c T a b : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) (X R : ℝ) : ℂ :=
  ∫ t : ℝ, rectangularVStarSelectedFiniteIntegrand diagonal c T a b σ f g Φ X R t

def rectangularVStarSelectedFiniteRemainderMoment (diagonal : Bool) (c T a b : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ→ℝ) (X R : ℝ) : ℂ :=
  ∫ t : ℝ, rectangularVStarSelectedFiniteRemainderIntegrand diagonal c T a b σ f g Φ X R t

theorem bblrVStarSelectedSmoothProductTail_summable (diagonal : Bool) (T : ℝ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (u w : ℕ) (t X : ℝ) :
    Summable (fun n : Fin 4→ℕ => (rectangularAFESmoothTailWeight X n:ℂ)*
      (if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true) then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0)) := by
  apply (bblrVStarSelectedAFE_norm_summable diagonal T σ α hα u w t).of_norm_bounded
  intro n
  have hW := rectangular_AFE_smooth_tail_weight_bounds X n
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hW.1]
  exact mul_le_of_le_one_left (norm_nonneg _) hW.2

theorem bblrVStarSelectedAFESum_eq_finite_grid (diagonal : Bool) (c T : ℝ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (u w : ℕ) (t X R : ℝ) :
    bblrVStarSelectedAFESum diagonal (polarPoleKiller T σ) α u w t=
      bblrVStarSelectedFiniteCore diagonal c T σ α u w t X R+
        bblrVStarSelectedFiniteRemainder diagonal c T σ α u w t X R := by
  have he := rectangular_AFE_smooth_grid_series_identity
    (fun n => if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true) then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0)
    (bblrVStarSelectedAFE_summable diagonal T σ α hα u w t) X
  change bblrVStarSelectedAFESum diagonal (polarPoleKiller T σ) α u w t=
    bblrVStarSelectedSmoothProductGrid diagonal (polarPoleKiller T σ) α u w t X+
      bblrVStarSelectedSmoothProductTail diagonal (polarPoleKiller T σ) α u w t X at he
  rw [he]
  unfold bblrVStarSelectedFiniteRemainder
  suffices hgrid : bblrVStarSelectedSmoothProductGrid diagonal (polarPoleKiller T σ) α u w t X=
      bblrVStarSelectedFiniteCore diagonal c T σ α u w t X R+
        bblrVStarSelectedGridFrequencyTail diagonal c T σ α u w t X R by rw [hgrid]; ring
  unfold bblrVStarSelectedSmoothProductGrid bblrVStarSelectedFiniteCore bblrVStarSelectedGridFrequencyTail
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> ring

theorem rectangularVStarSelectedCombinedIntegrand_eq_finite_grid (diagonal : Bool) (c T a b : ℝ)
    (σ : MomentShifts) (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4)
    (f g Φ : ℝ→ℝ) (X R t : ℝ) :
    rectangularVStarSelectedCombinedIntegrand diagonal T a b σ f g Φ t=
      rectangularVStarSelectedFiniteIntegrand diagonal c T a b σ f g Φ X R t+
        rectangularVStarSelectedFiniteRemainderIntegrand diagonal c T a b σ f g Φ X R t := by
  unfold rectangularVStarSelectedCombinedIntegrand rectangularVStarSelectedIntegrand
    rectangularVStarSelectedFiniteIntegrand rectangularVStarSelectedFiniteRemainderIntegrand
  simp only [Finset.mul_sum]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u _
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w _
  rw [bblrVStarSelectedAFESum_eq_finite_grid diagonal c T σ _ hα u w t X R,
    bblrVStarSelectedAFESum_eq_finite_grid diagonal c T σ _
      (bblrSixShifts_norm_le _ hα 1) u w t X R]
  ring

theorem bblrVStarSelectedFiniteCore_time_stronglyMeasurable {c : ℝ} (hc : 0<c)
    (diagonal : Bool) (T : ℝ) (σ α : MomentShifts) (u w : ℕ) (X R : ℝ) :
    StronglyMeasurable (fun t : ℝ => bblrVStarSelectedFiniteCore diagonal c T σ α u w t X R) := by
  have he : (fun t : ℝ => bblrVStarSelectedFiniteCore diagonal c T σ α u w t X R)=
      ∑ k∈rectangularAFEProductScaleGrid X, ∑ n∈rectangularAFESmoothBox k,
        fun t : ℝ => (rectangularAFESmoothWeight k n:ℂ)*
          (if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true) then bblrGaussianVStarCoreSummand c T σ α t R n else 0) := by
    funext t
    simp only [bblrVStarSelectedFiniteCore,Finset.sum_apply]
  rw [he]
  apply Finset.stronglyMeasurable_sum
  intro k _
  apply Finset.stronglyMeasurable_sum
  intro n _
  by_cases hn : diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true
  · simp only [hn,ite_true]
    exact (bblrGaussianVStarCoreSummand_time_stronglyMeasurable hc T σ α R n).const_mul _
  · simp only [hn,ite_false,mul_zero]
    exact stronglyMeasurable_const

theorem bblrVStarSelectedAFESum_time_stronglyMeasurable (diagonal : Bool)
    (G : ℂ→ℂ) (hG : Continuous G) (α : MomentShifts) (u w : ℕ) :
    StronglyMeasurable (bblrVStarSelectedAFESum diagonal G α u w) := by
  apply StronglyMeasurable.tsum
  intro n
  by_cases hn : diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true
  · simp only [hn,ite_true]
    exact bblrVStarAFESummand_time_stronglyMeasurable G hG α n
  · simp only [hn,ite_false]
    exact stronglyMeasurable_const

theorem bblrVStarSelectedFiniteRemainder_time_stronglyMeasurable {c : ℝ} (hc : 0<c)
    (diagonal : Bool) (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4)
    (u w : ℕ) (X R : ℝ) :
    StronglyMeasurable (fun t : ℝ => bblrVStarSelectedFiniteRemainder diagonal c T σ α u w t X R) := by
  have he : (fun t : ℝ => bblrVStarSelectedFiniteRemainder diagonal c T σ α u w t X R)=
      (fun t : ℝ => bblrVStarSelectedAFESum diagonal (polarPoleKiller T σ) α u w t)-
        (fun t : ℝ => bblrVStarSelectedFiniteCore diagonal c T σ α u w t X R) := by
    funext t
    have h := bblrVStarSelectedAFESum_eq_finite_grid diagonal c T σ α hα u w t X R
    simp only [Pi.sub_apply]
    linear_combination -h
  rw [he]
  exact (bblrVStarSelectedAFESum_time_stronglyMeasurable diagonal _
    (polarPoleKiller_differentiable T σ).continuous α u w).sub
      (bblrVStarSelectedFiniteCore_time_stronglyMeasurable hc diagonal T σ α u w X R)

end
end SixthMoment
