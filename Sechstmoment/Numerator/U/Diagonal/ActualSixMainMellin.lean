import Sechstmoment.Numerator.U.Diagonal.ActualDiagonalTime
import Sechstmoment.Numerator.U.Diagonal.ActualFiniteAmplifiers

/-! A direct identity for the literal six source main terms, with actual finite
amplifier supports, dyadic time integrability, profile inversion, and Euler sums. -/

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

private theorem actualFiniteDiagonal_dyadic_integrable {T a b : ℝ} (hT : 0 < T)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (ρ : ℂ) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*(t/(2*π):ℂ)^ρ*
      (∑ m ∈ Finset.Icc 1 ⌊T^a⌋₊, ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊,
        (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*bblrDiagonalTerm G α m n t)) := by
  have hi : Integrable (fun t : ℝ => ∑ m ∈ Finset.Icc 1 ⌊T^a⌋₊,
      ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊, ((f (Real.log m/Real.log T):ℂ)*
        (g (Real.log n/Real.log T):ℂ))*
          ((Φ (t/T):ℂ)*(t/(2*π):ℂ)^ρ*bblrDiagonalTerm G α m n t)) := by
    apply integrable_finsetSum
    intro m hm
    apply integrable_finsetSum
    intro n hn
    exact (actualDyadicDiagonal_integrable hT G α hG hα Φ hΦ ρ m n).const_mul _
  convert hi using 1
  funext t
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem actualFiniteAmplifiedDiagonal_time_integral {T a b : ℝ} (hT : 0 < T)
    (G : ℂ → ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α)
    (hα : ∀ j, -1/2 < (α j).re) (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (ρ : ℂ) :
    (∑ m ∈ Finset.Icc 1 ⌊T^a⌋₊, ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊,
      (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*
        ∫ t : ℝ, (Φ (t/T):ℂ)*(t/(2*π):ℂ)^ρ*bblrDiagonalTerm G α m n t) =
      ∫ t : ℝ, (Φ (t/T):ℂ)*(t/(2*π):ℂ)^ρ*
        (∑ m ∈ Finset.Icc 1 ⌊T^a⌋₊, ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊,
          (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*bblrDiagonalTerm G α m n t) := by
  symm
  calc
    _ = ∫ t : ℝ, ∑ m ∈ Finset.Icc 1 ⌊T^a⌋₊, ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊,
        ((f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ))*
          ((Φ (t/T):ℂ)*(t/(2*π):ℂ)^ρ*bblrDiagonalTerm G α m n t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = _ := by
      rw [integral_finsetSum (Finset.Icc 1 ⌊T^a⌋₊) (fun m hm =>
        integrable_finsetSum (Finset.Icc 1 ⌊T^b⌋₊) (fun n hn =>
          (actualDyadicDiagonal_integrable hT G α hG hα Φ hΦ ρ m n).const_mul _))]
      apply Finset.sum_congr rfl
      intro m hm
      rw [integral_finsetSum (Finset.Icc 1 ⌊T^b⌋₊) (fun n hn =>
        (actualDyadicDiagonal_integrable hT G α hG hα Φ hΦ ρ m n).const_mul _)]
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_const_mul _ _

private theorem actualSmallShifts_re_lower {δ : ℝ} (hδ1 : δ ≤ 1)
    (α : MomentShifts) (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4) :
    ∀ j : Fin 4, -1/2 < (α j).re := by
  intro j
  have h := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
  linarith

private theorem actualDyadic_weightedFinite_eq_Mellin {T a b δ : ℝ} (hT : 1 < T)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (ρ : ℂ) (t : ℝ) :
    (Φ (t/T):ℂ)*(t/(2*π):ℂ)^ρ*
      (∑ m ∈ Finset.Icc 1 ⌊T^a⌋₊, ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊,
        (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*bblrDiagonalTerm G α m n t) =
      (Φ (t/T):ℂ)*(t/(2*π):ℂ)^ρ*
        ((1/(2*π):ℂ)*((Real.log T:ℂ)/(2*π))^2*
          ∫ w : ℝ × (ℝ × ℝ), actualTripleMellinEulerKernel G α
            (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) (Real.log T) δ t w
            ∂(volume.prod (volume.prod volume))) := by
  by_cases ht : t ≠ 0
  · rw [actualFiniteAmplifiedDiagonal_eq_MellinEuler hT ht hδ hδ1 G α hG f g hf hg hα]
  · have ht0 : t=0 := not_ne_iff.mp ht
    have hΦ0 : Φ 0=0 := by
      by_contra hn
      have hs := hΦ.2 (subset_tsupport Φ hn)
      simp only [Set.mem_Icc] at hs
      linarith [hs.1]
    simp only [ht0,zero_div,hΦ0,Complex.ofReal_zero,zero_mul]

theorem actualFiniteAmplifiedDiagonal_dyadic_eq_MellinEuler {T a b δ : ℝ} (hT : 1 < T)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (ρ : ℂ) :
    (∑ m ∈ Finset.Icc 1 ⌊T^a⌋₊, ∑ n ∈ Finset.Icc 1 ⌊T^b⌋₊,
      (f (Real.log m/Real.log T):ℂ)*(g (Real.log n/Real.log T):ℂ)*
        ∫ t : ℝ, (Φ (t/T):ℂ)*(t/(2*π):ℂ)^ρ*bblrDiagonalTerm G α m n t) =
      ∫ t : ℝ, (Φ (t/T):ℂ)*(t/(2*π):ℂ)^ρ*
        ((1/(2*π):ℂ)*((Real.log T:ℂ)/(2*π))^2*
          ∫ w : ℝ × (ℝ × ℝ), actualTripleMellinEulerKernel G α
            (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) (Real.log T) δ t w
            ∂(volume.prod (volume.prod volume))) := by
  rw [actualFiniteAmplifiedDiagonal_time_integral (zero_lt_one.trans hT) G α hG
    (actualSmallShifts_re_lower hδ1 α hα) f g Φ hΦ ρ]
  apply integral_congr_ae
  exact Eventually.of_forall (actualDyadic_weightedFinite_eq_Mellin hT hδ hδ1 G α hG hα
    f g Φ hf hg hΦ ρ)

theorem bblrSixMainTerms_eq_actualMellinEuler {T a b δ : ℝ} (hT : 1 < T)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (G : ℂ → ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (f g Φ : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) :
    bblrSixMainTerms T a b α G f g Φ =
      ∫ t : ℝ, ∑ j : Fin 6,
        (Φ (t/T):ℂ)*(t/(2*π):ℂ)^(bblrSixPhaseExponents α j)*
          ((1/(2*π):ℂ)*((Real.log T:ℂ)/(2*π))^2*
            ∫ w : ℝ × (ℝ × ℝ), actualTripleMellinEulerKernel G (bblrSixShifts α j)
              (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) (Real.log T) δ t w
              ∂(volume.prod (volume.prod volume))) := by
  have hshift (j : Fin 6) (k : Fin 4) : ‖bblrSixShifts α j k‖ ≤ δ/4 :=
    bblrSixShifts_norm_le α hα j k
  have hi (j : Fin 6) : Integrable (fun t : ℝ =>
      (Φ (t/T):ℂ)*(t/(2*π):ℂ)^(bblrSixPhaseExponents α j)*
        ((1/(2*π):ℂ)*((Real.log T:ℂ)/(2*π))^2*
          ∫ w : ℝ × (ℝ × ℝ), actualTripleMellinEulerKernel G (bblrSixShifts α j)
            (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) (Real.log T) δ t w
            ∂(volume.prod (volume.prod volume)))) := by
    apply (actualFiniteDiagonal_dyadic_integrable (zero_lt_one.trans hT) G
      (bblrSixShifts α j) hG (actualSmallShifts_re_lower hδ1 _ (hshift j))
      f g Φ hΦ (bblrSixPhaseExponents α j)).congr
    exact Eventually.of_forall (actualDyadic_weightedFinite_eq_Mellin hT hδ hδ1 G
      (bblrSixShifts α j) hG (hshift j) f g Φ hf hg hΦ (bblrSixPhaseExponents α j))
  rw [integral_finsetSum Finset.univ (fun j _ => hi j)]
  unfold bblrSixMainTerms
  apply Finset.sum_congr rfl
  intro j hj
  exact actualFiniteAmplifiedDiagonal_dyadic_eq_MellinEuler hT hδ hδ1 G (bblrSixShifts α j)
    hG (hshift j) f g Φ hf hg hΦ (bblrSixPhaseExponents α j)

end
end Sechstmoment
