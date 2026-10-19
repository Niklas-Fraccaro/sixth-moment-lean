import Sechstmoment.Zeta.DirichletL.PrimitiveFourthMoment

/-! Extension of the fourth moment to every nonprincipal character. These
are exactly the characters in the error term of the V-generator reduction.
The principal character belongs to the separately evaluated main term.
-/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators Classical
noncomputable section

theorem dirichletEulerFactors_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ _ : NeZero N,
      ∀ M : ℕ, ∀ _ : NeZero M, ∀ χ : DirichletCharacter ℂ M,
      ∀ s : ℂ, 0 ≤ s.re →
      ‖∏ p ∈ N.primeFactors, (1-χ p*(p : ℂ)^(-s))‖ ≤ C*(N : ℝ)^ε := by
  obtain ⟨D,hD,hbound⟩ := divisor_prime_cost_subpower hε (by norm_num : (1 : ℝ) ≤ 2)
  refine ⟨D+1, by positivity, ?_⟩
  intro N hN M hM χ s hs
  have : NeZero N := hN
  have : NeZero M := hM
  have hlocal (p : ℕ) (hp : p ∈ N.primeFactors) : ‖1-χ p*(p : ℂ)^(-s)‖ ≤ 2 := by
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpow : ‖(p : ℂ)^(-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp'.pos, neg_re]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp'.one_le) (by linarith)
    calc
      _ ≤ ‖(1 : ℂ)‖+‖χ p*(p : ℂ)^(-s)‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one,norm_mul]; nlinarith [χ.norm_le_one (p : ZMod M),norm_nonneg (χ p)]
  have hcard : (1 : ℝ) ≤ N.divisors.card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1,Nat.one_mem_divisors.mpr (NeZero.ne N)⟩
  have h := hbound N (NeZero.ne N)
  calc
    _ = ∏ p ∈ N.primeFactors, ‖1-χ p*(p : ℂ)^(-s)‖ := norm_prod _ _
    _ ≤ ∏ _p ∈ N.primeFactors, (2 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hlocal
    _ = (2 : ℝ)^N.primeFactors.card := by simp
    _ ≤ (N.divisors.card : ℝ)*(2 : ℝ)^N.primeFactors.card :=
      le_mul_of_one_le_left (by positivity) hcard
    _ ≤ D*(N : ℝ)^ε := h
    _ ≤ _ := by gcongr; linarith

theorem dirichletL_changeLevel_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ _ : NeZero N,
      ∀ M : ℕ, ∀ _ : NeZero M, ∀ hMN : M ∣ N,
      ∀ χ : DirichletCharacter ℂ M, ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (3/4) →
      ‖(DirichletCharacter.changeLevel hMN χ).LFunction s‖ ≤
        C*(N : ℝ)^ε*‖χ.LFunction s‖ := by
  obtain ⟨C,hC,hbound⟩ := dirichletEulerFactors_subpower hε
  refine ⟨C,hC,?_⟩
  intro N hN M hM hMN χ s hs
  have : NeZero N := hN
  have : NeZero M := hM
  have hs1 : s ≠ 1 := by intro h; have hr := congrArg Complex.re h; simp at hr; linarith [hs.2]
  rw [DirichletCharacter.LFunction_changeLevel hMN χ (Or.inr hs1), norm_mul]
  calc
    _ ≤ ‖χ.LFunction s‖*(C*(N : ℝ)^ε) :=
      mul_le_mul_of_nonneg_left (hbound N hN M hM χ s (by linarith [hs.1])) (norm_nonneg _)
    _ = _ := by ring

instance divisorLevel_neZero {N : ℕ} [NeZero N] (r : N.divisors) : NeZero r.val :=
  ⟨ne_zero_of_dvd_ne_zero (NeZero.ne N) (Nat.dvd_of_mem_divisors r.property)⟩

abbrev DirichletConductorSource (N : ℕ) [NeZero N] :=
  Σ r : N.divisors, {χ : DirichletCharacter ℂ r.val // χ.IsPrimitive ∧ χ ≠ 1}

def conductorSourceLift {N : ℕ} [NeZero N] (t : DirichletConductorSource N) :
    DirichletCharacter ℂ N :=
  DirichletCharacter.changeLevel (Nat.dvd_of_mem_divisors t.1.property) t.2.val

def nonprincipalConductorSource {N : ℕ} [NeZero N]
    (χ : {χ : DirichletCharacter ℂ N // χ ≠ 1}) : DirichletConductorSource N := by
  let r : N.divisors := ⟨χ.val.conductor,Nat.mem_divisors.mpr ⟨χ.val.conductor_dvd_level,NeZero.ne N⟩⟩
  refine ⟨r,χ.val.primitiveCharacter,χ.val.primitiveCharacter_isPrimitive,?_⟩
  intro h
  have he := χ.val.changeLevel_primitiveCharacter
  rw [h,map_one] at he
  exact χ.property he.symm

theorem conductorSourceLift_pick {N : ℕ} [NeZero N]
    (χ : {χ : DirichletCharacter ℂ N // χ ≠ 1}) :
    conductorSourceLift (nonprincipalConductorSource χ) = χ.val :=
  χ.val.changeLevel_primitiveCharacter

theorem nonprincipalConductorSource_injective {N : ℕ} [NeZero N] :
    Function.Injective (nonprincipalConductorSource (N := N)) := by
  intro χ ψ h
  apply Subtype.ext
  have he := congrArg conductorSourceLift h
  simpa only [conductorSourceLift_pick] using he

theorem nonprincipalDirichlet_fourthMoment {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ _ : NeZero N,
      ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (3/4) →
      (∑ χ : DirichletCharacter ℂ N with χ ≠ 1, ‖χ.LFunction s‖^4) ≤
        C*(N : ℝ)^(1+ε)*(1+|s.im|)^20 := by
  obtain ⟨A,hA,hEuler⟩ := dirichletL_changeLevel_subpower (ε := ε/16) (by linarith)
  obtain ⟨B,hB,hPrim⟩ := primitiveDirichlet_fourthMoment (ε := ε/2) (by linarith)
  obtain ⟨D,hD,hdiv⟩ := divisor_prime_cost_subpower (ε := ε/4) (C := 1) (by linarith) (by norm_num)
  refine ⟨A^4*B*(D+1), by positivity, ?_⟩
  intro N hN s hs
  have : NeZero N := hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  let E : ℝ := (A*(N : ℝ)^(ε/16))^4
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let f : DirichletConductorSource N → ℝ := fun t => ‖t.2.val.LFunction s‖^4
  have hpoint (χ : {χ : DirichletCharacter ℂ N // χ ≠ 1}) :
      ‖χ.val.LFunction s‖^4 ≤ E*f (nonprincipalConductorSource χ) := by
    have h := hEuler N hN (nonprincipalConductorSource χ).1.val inferInstance
      (Nat.dvd_of_mem_divisors (nonprincipalConductorSource χ).1.property)
      (nonprincipalConductorSource χ).2.val s hs
    change ‖(conductorSourceLift (nonprincipalConductorSource χ)).LFunction s‖ ≤ _ at h
    rw [conductorSourceLift_pick] at h
    change ‖χ.val.LFunction s‖^4 ≤ (A*(N : ℝ)^(ε/16))^4*‖(nonprincipalConductorSource χ).2.val.LFunction s‖^4
    rw [← mul_pow]
    gcongr
  have hsource (r : N.divisors) :
      (∑ ψ : {ψ : DirichletCharacter ℂ r.val // ψ.IsPrimitive ∧ ψ ≠ 1}, ‖ψ.val.LFunction s‖^4) ≤
        B*(N : ℝ)^(1+ε/2)*(1+|s.im|)^20 := by
    have h := hPrim r.val inferInstance s hs
    rw [Finset.sum_subtype (p := fun ψ : DirichletCharacter ℂ r.val => ψ.IsPrimitive ∧ ψ ≠ 1)
      _ (by simp) (fun ψ => ‖ψ.LFunction s‖^4)] at h
    exact h.trans (by
      gcongr
      exact_mod_cast Nat.divisor_le r.property)
  have hsources : (∑ t : DirichletConductorSource N, f t) ≤
      (N.divisors.card : ℝ)*(B*(N : ℝ)^(1+ε/2)*(1+|s.im|)^20) := by
    rw [Fintype.sum_sigma]
    calc
      _ ≤ ∑ _r : N.divisors, B*(N : ℝ)^(1+ε/2)*(1+|s.im|)^20 :=
        Finset.sum_le_sum (fun r _ => hsource r)
      _ = _ := by simp
  have hcard : (N.divisors.card : ℝ) ≤ (D+1)*(N : ℝ)^(ε/4) := by
    have h := hdiv N (NeZero.ne N)
    simp only [one_pow,mul_one] at h
    exact h.trans (by gcongr; linarith)
  rw [Finset.sum_subtype (p := fun χ : DirichletCharacter ℂ N => χ ≠ 1)
    _ (by simp) (fun χ => ‖χ.LFunction s‖^4)]
  calc
    _ ≤ ∑ χ : {χ : DirichletCharacter ℂ N // χ ≠ 1}, E*f (nonprincipalConductorSource χ) :=
      Finset.sum_le_sum (fun χ _ => hpoint χ)
    _ ≤ ∑ t : DirichletConductorSource N, E*f t := by
      exact Finset.sum_le_sum_of_injOn nonprincipalConductorSource
        nonprincipalConductorSource_injective.injOn (Finset.subset_univ _) (fun _ _ => le_rfl)
        (fun _ _ _ => by dsimp [f]; positivity)
    _ = E*(∑ t : DirichletConductorSource N, f t) := (Finset.mul_sum ..).symm
    _ ≤ E*((N.divisors.card : ℝ)*(B*(N : ℝ)^(1+ε/2)*(1+|s.im|)^20)) :=
      mul_le_mul_of_nonneg_left hsources hE
    _ ≤ E*(((D+1)*(N : ℝ)^(ε/4))*(B*(N : ℝ)^(1+ε/2)*(1+|s.im|)^20)) := by gcongr
    _ = _ := by
      have hp : ((N : ℝ)^(ε/16))^4 = (N : ℝ)^(ε/4) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
        congr 1
        ring
      have hprod : (N : ℝ)^(ε/4)*(N : ℝ)^(ε/4)*(N : ℝ)^(1+ε/2) = (N : ℝ)^(1+ε) := by
        rw [← Real.rpow_add hNr, ← Real.rpow_add hNr]
        congr 1
        ring
      dsimp only [E]
      rw [mul_pow,hp]
      calc
        _ = (A^4*B*(D+1))*((N : ℝ)^(ε/4)*(N : ℝ)^(ε/4)*(N : ℝ)^(1+ε/2))*(1+|s.im|)^20 := by ring
        _ = _ := by rw [hprod]

end
end Sechstmoment.Source
