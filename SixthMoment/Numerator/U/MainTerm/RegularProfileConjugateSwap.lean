import SixthMoment.Numerator.U.MainTerm.RegularProfileGenerator
import SixthMoment.Numerator.U.TwistedMomentHolomorphy

namespace SixthMoment
open Complex MeasureTheory Set
open scoped Topology ComplexConjugate
noncomputable section
set_option maxHeartbeats 1000000

private def alternantSwapIndex : Fin 4 → Fin 4 := ![2,3,0,1]
private def alternantReverseIndex : Fin 4 → Fin 4 := ![3,2,1,0]

private def alternantConjugateSwapSources (x : Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun j => -conj (x (alternantSwapIndex j))

private theorem determinant_four_swap_reverse (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (Matrix.of (fun i j => M (alternantSwapIndex i) (alternantReverseIndex j))).det = M.det := by
  rw [determinant_four_six_minors, determinant_four_six_minors]
  norm_num [matrixMinorTwo, alternantSwapIndex, alternantReverseIndex]
  ring

private theorem determinant_four_conj (M : Matrix (Fin 4) (Fin 4) ℂ) :
    (Matrix.of (fun i j => conj (M i j))).det = conj M.det := by
  rw [determinant_four_six_minors, determinant_four_six_minors]
  simp only [matrixMinorTwo, Matrix.of_apply, map_add, map_sub, map_mul]

private theorem fourVandermonde_conjugateSwap (x : Fin 4 → ℂ) :
    fourVandermonde (alternantConjugateSwapSources x) = conj (fourVandermonde x) := by
  norm_num [fourVandermonde, alternantConjugateSwapSources, alternantSwapIndex,
    map_sub, map_mul]
  ring

theorem exponentialAlternant_conj_swap (x : Fin 4 → ℂ) (A B : ℝ) :
    conj (exponentialAlternant x (numeratorRho A B)) =
      exponentialAlternant (alternantConjugateSwapSources x) (numeratorRho B A) := by
  let M := expAlternantMatrix x (numeratorRho A B)
  have hmat : expAlternantMatrix (alternantConjugateSwapSources x) (numeratorRho B A) =
      Matrix.diagonal (fun i => Complex.exp (conj (x (alternantSwapIndex i)))) *
        Matrix.of (fun i j => conj (M (alternantSwapIndex i) (alternantReverseIndex j))) := by
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.of_apply]
    change Complex.exp (-conj (x (alternantSwapIndex i))*numeratorRho B A j) = _
    unfold M expAlternantMatrix
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    fin_cases j <;> norm_num [numeratorRho, alternantReverseIndex, map_mul, map_sub] <;> ring
  have hdiag : (Matrix.diagonal (fun i : Fin 4 =>
      Complex.exp (conj (x (alternantSwapIndex i))))).det =
      Complex.exp (conj (x 0+x 1+x 2+x 3)) := by
    rw [Matrix.det_diagonal]
    simp only [Fin.prod_univ_succ, alternantSwapIndex, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one]
    simp only [← Complex.exp_add, map_add]
    congr 1
    ring
  have hdet : (expAlternantMatrix (alternantConjugateSwapSources x) (numeratorRho B A)).det =
      Complex.exp (conj (x 0+x 1+x 2+x 3))*conj M.det := by
    have hp := determinant_four_swap_reverse (Matrix.of (fun i j => conj (M i j)))
    simp only [Matrix.of_apply] at hp
    rw [hmat, Matrix.det_mul, hdiag, hp, determinant_four_conj]
  have hexp : Complex.exp ((alternantConjugateSwapSources x) 0+
      (alternantConjugateSwapSources x) 1)*Complex.exp (conj (x 0+x 1+x 2+x 3)) =
      Complex.exp (conj (x 0+x 1)) := by
    rw [← Complex.exp_add]
    congr 1
    norm_num [alternantConjugateSwapSources, alternantSwapIndex, map_add]
    ring
  unfold exponentialAlternant
  rw [hdet, fourVandermonde_conjugateSwap, ← mul_assoc, hexp]
  simp only [map_div₀, map_mul, ← Complex.exp_conj, M]

private theorem alternantConjugateSwapSources_injective (x : Fin 4 → ℂ)
    (hx : Function.Injective x) : Function.Injective (alternantConjugateSwapSources x) := by
  have hp : Function.Injective alternantSwapIndex := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [alternantSwapIndex]
  intro i j h
  apply hp
  apply hx
  apply (starRingEnd ℂ).injective
  exact neg_injective h

theorem exponentialAlternantRegularized_conj_swap (x : Fin 4 → ℂ) (A B : ℝ) :
    conj (exponentialAlternantRegularized x (numeratorRho A B)) =
      exponentialAlternantRegularized (alternantConjugateSwapSources x) (numeratorRho B A) := by
  have hc : Continuous (fun x : Fin 4 → ℂ =>
      conj (exponentialAlternantRegularized x (numeratorRho A B))) :=
    Complex.continuous_conj.comp (exponentialAlternantRegularized_continuous_joint.comp
      (continuous_id.prodMk continuous_const))
  have hd : Continuous (fun x : Fin 4 → ℂ =>
      exponentialAlternantRegularized (alternantConjugateSwapSources x) (numeratorRho B A)) :=
    exponentialAlternantRegularized_continuous_joint.comp
      (by unfold alternantConjugateSwapSources; fun_prop : Continuous
        (fun x : Fin 4 → ℂ => (alternantConjugateSwapSources x,numeratorRho B A)))
  have hsub : {x : Fin 4 → ℂ | Function.Injective x} ⊆
      {x : Fin 4 → ℂ |
        conj (exponentialAlternantRegularized x (numeratorRho A B)) =
          exponentialAlternantRegularized (alternantConjugateSwapSources x) (numeratorRho B A)} := by
    intro y hy
    change conj (exponentialAlternantRegularized y (numeratorRho A B)) =
      exponentialAlternantRegularized (alternantConjugateSwapSources y) (numeratorRho B A)
    rw [exponentialAlternantRegularized_eq_raw _ _ hy,
      exponentialAlternantRegularized_eq_raw _ _ (alternantConjugateSwapSources_injective y hy)]
    exact exponentialAlternant_conj_swap y A B
  exact (closure_minimal hsub (isClosed_eq hc hd))
    (fourSourceShifts_injective_dense x)

private theorem conjugate_intervalIntegral (F : ℝ → ℂ) (a b : ℝ) :
    conj (∫ t in a..b, F t) = ∫ t in a..b, conj (F t) := by
  unfold intervalIntegral
  simp only [map_sub, ← integral_conj]

private theorem sourceKnots_twistedConjugateSwap (σ : Fin 4 → ℂ) :
    polarSourceKnots (twistedConjugateSwapShifts σ) =
      alternantConjugateSwapSources (polarSourceKnots σ) := by
  funext j
  fin_cases j <;> simp [polarSourceKnots, twistedConjugateSwapShifts,
    alternantConjugateSwapSources, alternantSwapIndex]

theorem actualRegularProfileKernel_conj_swap (σ : Fin 4 → ℂ) (A B : ℝ) :
    conj (actualRegularProfileKernel σ A B) =
      actualRegularProfileKernel (twistedConjugateSwapShifts σ) B A := by
  unfold actualRegularProfileKernel
  rw [conjugate_intervalIntegral]
  simp_rw [exponentialAlternantRegularized_conj_swap,
    ← sourceKnots_twistedConjugateSwap, min_comm A B]

theorem actualRegularProfileGenerator_conj_swap
    (a b : ℝ) (f g Φ : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (σ : Fin 4 → ℂ) :
    conj (actualRegularProfileGenerator a b (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ
      (twistedConjugateSwapShifts σ)) =
      actualRegularProfileGenerator b a (fun x => (g x:ℂ)) (fun x => (f x:ℂ)) Φ σ := by
  have hinvol : twistedConjugateSwapShifts (twistedConjugateSwapShifts σ) = σ := by
    funext j
    fin_cases j <;> simp [twistedConjugateSwapShifts]
  rw [actualRegularProfileGenerator_swap_integrals a b
    (fun x => (f x:ℂ)) (fun x => (g x:ℂ)) Φ
      (Complex.continuous_ofReal.comp hf) (Complex.continuous_ofReal.comp hg)]
  unfold actualRegularProfileGenerator
  simp only [map_mul, conj_ofReal, ← integral_conj, conjugate_intervalIntegral]
  simp_rw [actualRegularProfileKernel_conj_swap, hinvol]

end
end SixthMoment
