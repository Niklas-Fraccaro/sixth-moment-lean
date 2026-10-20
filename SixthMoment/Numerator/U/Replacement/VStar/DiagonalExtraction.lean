import SixthMoment.Numerator.U.Replacement.AmplifiedVStarFiniteGrid
import SixthMoment.Numerator.U.Separation.ActualGapPhase

namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

def bblrVStarSelectedAFESum (diagonal : Bool) (G : ℂ → ℂ) (α : MomentShifts)
    (u w : ℕ) (t : ℝ) : ℂ :=
  ∑' n : Fin 4 → ℕ, if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true)
    then bblrVStarAFESummand G α t n else 0

def rectangularVStarSelectedIntegrand (diagonal : Bool) (T a b : ℝ)
    (σ α : MomentShifts) (f g Φ : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    rectangularMomentPairWeight T f g Φ u w t*
      bblrVStarSelectedAFESum diagonal (polarPoleKiller T σ) α u w t

def rectangularVStarSelectedCombinedIntegrand (diagonal : Bool) (T a b : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ → ℝ) (t : ℝ) : ℂ :=
  rectangularVStarSelectedIntegrand diagonal T a b σ (rawMomentShifts T σ) f g Φ t+
    bblrDualLeadingMultiplier T σ (t/T)*
      rectangularVStarSelectedIntegrand diagonal T a b σ
        (bblrSixShifts (rawMomentShifts T σ) 1) f g Φ t

def rectangularVStarSelectedMoment (diagonal : Bool) (T a b : ℝ)
    (σ : MomentShifts) (f g Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, rectangularVStarSelectedCombinedIntegrand diagonal T a b σ f g Φ t

def bblrIndexedMainTerm (j : Fin 6) (T a b : ℝ) (α : MomentShifts) (G : ℂ → ℂ)
    (f g Φ : ℝ → ℝ) : ℂ :=
  ∑ m∈Finset.Icc 1 ⌊T^a⌋₊, ∑ n∈Finset.Icc 1 ⌊T^b⌋₊,
    (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*
      ∫ t : ℝ, (Φ (t/T):ℂ)*(t/(2*Real.pi):ℂ)^(bblrSixPhaseExponents α j)*
        bblrDiagonalTerm G (bblrSixShifts α j) m n t

theorem bblrSixMainTerms_eq_indexed (T a b : ℝ) (α : MomentShifts) (G : ℂ → ℂ)
    (f g Φ : ℝ → ℝ) :
    bblrSixMainTerms T a b α G f g Φ=∑ j : Fin 6, bblrIndexedMainTerm j T a b α G f g Φ := rfl

theorem bblrVStarSelectedAFE_norm_summable (diagonal : Bool) (T : ℝ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (u w : ℕ) (t : ℝ) :
    Summable (fun n : Fin 4 → ℕ => ‖if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true)
      then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0‖) := by
  have hs := bblrGaussianVStarAFE_norm_summable T σ α hα t
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (bblrVStarAFESummand (polarPoleKiller T σ) α t n)

theorem bblrVStarSelectedAFE_summable (diagonal : Bool) (T : ℝ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (u w : ℕ) (t : ℝ) :
    Summable (fun n : Fin 4 → ℕ => if (diagonalQuadRelation (u+1) (w+1) n ↔ diagonal=true)
      then bblrVStarAFESummand (polarPoleKiller T σ) α t n else 0) :=
  (bblrVStarSelectedAFE_norm_summable diagonal T σ α hα u w t).of_norm

theorem bblrVStarAFESum_eq_diagonal_add_offdiagonal (T : ℝ)
    (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) (u w : ℕ) (t : ℝ) :
    bblrVStarAFESum (polarPoleKiller T σ) α t=
      bblrVStarSelectedAFESum true (polarPoleKiller T σ) α u w t+
        bblrVStarSelectedAFESum false (polarPoleKiller T σ) α u w t := by
  unfold bblrVStarAFESum bblrVStarSelectedAFESum
  rw [←(bblrVStarSelectedAFE_summable true T σ α hα u w t).tsum_add
    (bblrVStarSelectedAFE_summable false T σ α hα u w t)]
  apply tsum_congr
  intro n
  by_cases hn : diagonalQuadRelation (u+1) (w+1) n <;> simp [hn]

theorem rectangular_VStar_moment_weight_eq_pair_sum {T : ℝ} (hT : 1<T) (a b : ℝ)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (t : ℝ) :
    rectangularMomentWeight T f g Φ t=
      ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        rectangularMomentPairWeight T f g Φ u w t := by
  unfold rectangularMomentWeight
  rw [profileDirichletSum_eq_finite hT a f (rectangular_supported_profile_zero_above f hf),
    profileDirichletSum_eq_finite hT b g (rectangular_supported_profile_zero_above g hg)]
  simp only [Finset.mul_sum,Finset.sum_mul,rectangularMomentPairWeight]
  rw [Finset.sum_comm]

theorem rectangularVStarAFEIntegrand_eq_selected {T : ℝ} (hT : 1<T) (a b : ℝ)
    (σ : MomentShifts) (hα : ∀ j, ‖rawMomentShifts T σ j‖≤1/4)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (t : ℝ) :
    rectangularVStarAFEIntegrand T σ f g Φ t=
      rectangularVStarSelectedCombinedIntegrand true T a b σ f g Φ t+
        rectangularVStarSelectedCombinedIntegrand false T a b σ f g Φ t := by
  have he (α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
      rectangularMomentWeight T f g Φ t*bblrVStarAFESum (polarPoleKiller T σ) α t=
        rectangularVStarSelectedIntegrand true T a b σ α f g Φ t+
          rectangularVStarSelectedIntegrand false T a b σ α f g Φ t := by
    rw [rectangular_VStar_moment_weight_eq_pair_sum hT a b f g Φ hf hg t]
    unfold rectangularVStarSelectedIntegrand
    simp only [Finset.sum_mul]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w _
    rw [bblrVStarAFESum_eq_diagonal_add_offdiagonal T σ α hα u w t,mul_add]
  unfold rectangularVStarAFEIntegrand rectangularVStarSelectedCombinedIntegrand
  rw [mul_add,show rectangularMomentWeight T f g Φ t*
      (bblrDualLeadingMultiplier T σ (t/T)*
        bblrVStarAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) t)=
      bblrDualLeadingMultiplier T σ (t/T)*(rectangularMomentWeight T f g Φ t*
        bblrVStarAFESum (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) 1) t) by ring,
    he _ hα,he _ (bblrSixShifts_norm_le _ hα 1)]
  ring

private theorem sum_range_succ_eq_Icc (N : ℕ) (H : ℕ→ℂ) :
    (∑ u∈Finset.range N, H (u+1))=∑ m∈Finset.Icc 1 N, H m := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega),ih]

theorem rectangular_actual_pair_VStar_diagonal (T : ℝ) (f g Φ : ℝ→ℝ)
    (G : ℂ→ℂ) (α : MomentShifts) (u w : ℕ) (t : ℝ) (n : Fin 4→ℕ)
    (hn : diagonalQuadRelation (u+1) (w+1) n) :
    rectangularMomentPairWeight T f g Φ u w t*bblrVStarAFESummand G α t n=
      (Φ (t/T):ℂ)*(f (Real.log (u+1:ℝ)/Real.log T):ℂ)*
        (g (Real.log (w+1:ℝ)/Real.log T):ℂ)*bblrDiagonalSummand G α (u+1) (w+1) t n := by
  have hphase : rectangularTwistedQuadPhase t (u+1) (w+1) n=1 := by
    unfold rectangularTwistedQuadPhase
    rw [hn,div_self (by exact_mod_cast (show (w+1)*(n 2+1)*(n 3+1)≠0 by positivity)),Complex.one_cpow]
  have hpow : (u+1:ℂ)^(-(1/2:ℂ))*(w+1:ℂ)^(-(1/2:ℂ))=
      (((u+1)*(w+1):ℕ):ℂ)^(-(1/2:ℂ)) := by
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Complex.ofReal_natCast,Complex.ofReal_add,Complex.ofReal_one] using
      (Complex.mul_cpow_ofReal_nonneg (by positivity : 0≤(u+1:ℝ))
        (by positivity : 0≤(w+1:ℝ)) (-(1/2:ℂ))).symm
  unfold bblrVStarAFESummand
  rw [mul_div_assoc,←mul_assoc,rectangular_actual_pair_weight_oscillation,hphase,mul_one]
  rw [show (Φ (t/T):ℂ)*(f (Real.log (u+1:ℝ)/Real.log T):ℂ)*
      (g (Real.log (w+1:ℝ)/Real.log T):ℂ)*(u+1:ℂ)^(-(1/2:ℂ))*(w+1:ℂ)^(-(1/2:ℂ))=
      ((Φ (t/T):ℂ)*(f (Real.log (u+1:ℝ)/Real.log T):ℂ)*
        (g (Real.log (w+1:ℝ)/Real.log T):ℂ))*
        ((u+1:ℂ)^(-(1/2:ℂ))*(w+1:ℂ)^(-(1/2:ℂ))) by ring]
  unfold bblrDiagonalSummand
  rw [hpow,Complex.cpow_neg]
  ring

theorem rectangular_pair_VStarSelected_diagonal (T : ℝ) (f g Φ : ℝ→ℝ)
    (G : ℂ→ℂ) (α : MomentShifts) (u w : ℕ) (t : ℝ) :
    rectangularMomentPairWeight T f g Φ u w t*bblrVStarSelectedAFESum true G α u w t=
      (Φ (t/T):ℂ)*(f (Real.log (u+1:ℝ)/Real.log T):ℂ)*
        (g (Real.log (w+1:ℝ)/Real.log T):ℂ)*bblrDiagonalTerm G α (u+1) (w+1) t := by
  unfold bblrVStarSelectedAFESum bblrDiagonalTerm
  rw [←tsum_mul_left,←tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : diagonalQuadRelation (u+1) (w+1) n
  · simpa only [hn,iff_self,ite_true,iff_true] using rectangular_actual_pair_VStar_diagonal T f g Φ G α u w t n hn
  · simp [hn]

theorem rectangularVStarSelectedIntegrand_diagonal_eq_source (T a b : ℝ)
    (σ α : MomentShifts) (f g Φ : ℝ→ℝ) (t : ℝ) :
    rectangularVStarSelectedIntegrand true T a b σ α f g Φ t=
      ∑ m∈Finset.Icc 1 ⌊T^a⌋₊, ∑ n∈Finset.Icc 1 ⌊T^b⌋₊,
        (Φ (t/T):ℂ)*(f (Real.log m/Real.log T):ℂ)*
          (g (Real.log n/Real.log T):ℂ)*bblrDiagonalTerm (polarPoleKiller T σ) α m n t := by
  unfold rectangularVStarSelectedIntegrand
  simp only [rectangular_pair_VStarSelected_diagonal]
  convert (sum_range_succ_eq_Icc ⌊T^a⌋₊ (fun m =>
    ∑ w∈Finset.range ⌊T^b⌋₊, (Φ (t/T):ℂ)*(f (Real.log m/Real.log T):ℂ)*
      (g (Real.log (w+1:ℕ)/Real.log T):ℂ)*bblrDiagonalTerm (polarPoleKiller T σ) α m (w+1) t)).trans ?_ using 1
  · push_cast
    rfl
  · apply Finset.sum_congr rfl
    intro m _
    exact sum_range_succ_eq_Icc ⌊T^b⌋₊ (fun n =>
      (Φ (t/T):ℂ)*(f (Real.log m/Real.log T):ℂ)*
        (g (Real.log n/Real.log T):ℂ)*bblrDiagonalTerm (polarPoleKiller T σ) α m n t)

end
end SixthMoment
