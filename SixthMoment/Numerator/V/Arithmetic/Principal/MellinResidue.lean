import SixthMoment.Numerator.V.Arithmetic.Principal.MellinNumerator


namespace SixthMoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem principalMellinNumerator_residue (q : ℕ) [NeZero q] (d : ℕ)
    (w : ℝ → ℂ) (β : Fin 4 → ℂ) (hβ : Function.Injective β) (x : ℝ) (i : Fin 4) :
    (((Finset.univ : Finset (Fin 4)).erase i).prod
      (fun j : Fin 4 => (1-β i)-(1-β j)))⁻¹*
        principalMellinNumerator q d w β x (1-β i) =
      mellin w (1-β i)*(x:ℂ)^(1-β i)*
        eulerCorrection (1 : DirichletCharacter ℂ q) d β (1-β i)*
        (∏ p ∈ q.primeFactors, (1-(p:ℂ)⁻¹))*
        (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          (1 : DirichletCharacter ℂ q).LFunction ((1-β i)+β j)) := by
  let S := (Finset.univ : Finset (Fin 4)).erase i
  let Q : ℂ := S.prod (fun j : Fin 4 => (1-β i)-(1-β j))
  let L : ℂ := ∏ j ∈ S, (1 : DirichletCharacter ℂ q).LFunction ((1-β i)+β j)
  let M : ℂ := ∏ p ∈ q.primeFactors, (1-(p:ℂ)⁻¹)
  have hsep (j : Fin 4) (hj : j ∈ S) : β j ≠ β i := by
    intro he
    exact (Finset.mem_erase.mp hj).1 (hβ he)
  have hQ : Q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro he
    exact hsep j hj (by linear_combination he)
  have hreg (j : Fin 4) (hj : j ∈ S) :
      DirichletCharacter.LFunctionTrivChar₁ q ((1-β i)+β j) =
        ((1-β i)-(1-β j))*(1 : DirichletCharacter ℂ q).LFunction ((1-β i)+β j) := by
    have hn : (1-β i)+β j ≠ 1 := by
      intro he
      exact hsep j hj (by linear_combination he)
    rw [DirichletCharacter.LFunctionTrivChar₁,Function.update_of_ne hn]
    congr 1
    ring
  have hregi : DirichletCharacter.LFunctionTrivChar₁ q ((1-β i)+β i) = M := by
    rw [sub_add_cancel]
    exact Function.update_self _ _ _
  have hprod : (∏ j : Fin 4, DirichletCharacter.LFunctionTrivChar₁ q ((1-β i)+β j)) =
      M*(Q*L) := by
    calc
      _ = DirichletCharacter.LFunctionTrivChar₁ q ((1-β i)+β i)*
          ∏ j ∈ S, DirichletCharacter.LFunctionTrivChar₁ q ((1-β i)+β j) :=
        (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm
      _ = M*(∏ j ∈ S, ((1-β i)-(1-β j))*
          (1 : DirichletCharacter ℂ q).LFunction ((1-β i)+β j)) := by
        rw [hregi]
        congr 1
        exact Finset.prod_congr rfl hreg
      _ = _ := by rw [Finset.prod_mul_distrib]
  change Q⁻¹*principalMellinNumerator q d w β x (1-β i) =
    mellin w (1-β i)*(x:ℂ)^(1-β i)*
      eulerCorrection (1 : DirichletCharacter ℂ q) d β (1-β i)*M*L
  rw [principalMellinNumerator,hprod]
  calc
    _ = (Q⁻¹*Q)*(mellin w (1-β i)*(x:ℂ)^(1-β i)*
        eulerCorrection (1 : DirichletCharacter ℂ q) d β (1-β i)*M*L) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hQ,one_mul]

theorem principal_residue_L_product_eq_zeta (q : ℕ) [NeZero q]
    (β : Fin 4 → ℂ) (hβ : Function.Injective β) (i : Fin 4) :
    (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
      (1 : DirichletCharacter ℂ q).LFunction ((1-β i)+β j)) =
      (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
        ∏ p ∈ q.primeFactors, (1-(p:ℂ)^(-(1+β j-β i))))*
      (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, riemannZeta (1+β j-β i)) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hne : 1+β j-β i ≠ 1 := by
    intro he
    have hbj : β j = β i := by linear_combination he
    exact (Finset.mem_erase.mp hj).1 (hβ hbj)
  rw [show (1-β i)+β j = 1+β j-β i by ring]
  exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := q) hne

end
end SixthMoment.Source.NoDPGlobalLFactorization
