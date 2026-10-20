import Sechstmoment.Numerator.V.Arithmetic.Additive.Characters
import Sechstmoment.Zeta.DirichletL.CharacterFourthMoment


namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set ZMod Finset
open scoped Topology BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

theorem modulus_le_totient_prime_cost (q : ℕ) [NeZero q] :
    (q : ℝ) ≤ (q.totient : ℝ)*(2 : ℝ)^q.primeFactors.card := by
  let B : ℝ := ∏ p ∈ q.primeFactors, ((p-1 : ℕ) : ℝ)
  have hB : 0 < B := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast Nat.sub_pos_of_lt (Nat.prime_of_mem_primeFactors hp).one_lt
  have he : (q.totient : ℝ)*(∏ p ∈ q.primeFactors, (p : ℝ)) = (q : ℝ)*B := by
    dsimp only [B]
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors q)
    simpa only [Nat.cast_mul,Nat.cast_prod] using h
  have hp : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ (2 : ℝ)^q.primeFactors.card*B := by
    calc
      _ ≤ ∏ p ∈ q.primeFactors, 2*((p-1 : ℕ) : ℝ) := by
        apply Finset.prod_le_prod₀ (fun p _ => Nat.cast_nonneg p)
        intro p hp
        have h : p ≤ 2*(p-1) := by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
        exact_mod_cast h
      _ = _ := by rw [Finset.prod_mul_distrib]; simp [B]
  have hmul : (q : ℝ)*B ≤ ((q.totient : ℝ)*(2 : ℝ)^q.primeFactors.card)*B := by
    calc
      _ = (q.totient : ℝ)*(∏ p ∈ q.primeFactors, (p : ℝ)) := he.symm
      _ ≤ (q.totient : ℝ)*((2 : ℝ)^q.primeFactors.card*B) :=
        mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
      _ = _ := by ring
  exact le_of_mul_le_mul_right hmul hB

theorem modulus_totient_ratio_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ _ : NeZero q,
      (q : ℝ)/(q.totient : ℝ) ≤ C*(q : ℝ)^ε := by
  obtain ⟨D,hD,hbound⟩ := divisor_prime_cost_subpower hε (by norm_num : (1 : ℝ) ≤ 2)
  refine ⟨D+1,by positivity,?_⟩
  intro q hq
  have : NeZero q := hq
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hcard : (1 : ℝ) ≤ q.divisors.card := by
    exact_mod_cast Finset.one_le_card.mpr ⟨1,Nat.one_mem_divisors.mpr (NeZero.ne q)⟩
  calc
    _ ≤ (2 : ℝ)^q.primeFactors.card := (div_le_iff₀ hφ).mpr (by
      simpa only [mul_comm] using modulus_le_totient_prime_cost q)
    _ ≤ (q.divisors.card : ℝ)*(2 : ℝ)^q.primeFactors.card :=
      le_mul_of_one_le_left (by positivity) hcard
    _ ≤ D*(q : ℝ)^ε := hbound q (NeZero.ne q)
    _ ≤ _ := by gcongr; linarith

def gaussFourLTransform (q : ℕ) [NeZero q] (s : Fin 4 → ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
    gaussSum χ⁻¹ stdAddChar * χ (-1) * ∏ j : Fin 4, χ.LFunction (s j)

theorem gaussFourLTransform_norm_le (q : ℕ) [NeZero q] (s : Fin 4 → ℂ) :
    ‖gaussFourLTransform q s‖ ≤
      (q.totient : ℝ)⁻¹*Real.sqrt q*
        ∑ χ : DirichletCharacter ℂ q, ∏ j : Fin 4, ‖χ.LFunction (s j)‖ := by
  have hsum : ‖∑ χ : DirichletCharacter ℂ q,
      gaussSum χ⁻¹ stdAddChar * χ (-1) * ∏ j : Fin 4, χ.LFunction (s j)‖ ≤
      Real.sqrt q * ∑ χ : DirichletCharacter ℂ q, ∏ j : Fin 4, ‖χ.LFunction (s j)‖ := by
    calc
      _ ≤ ∑ χ : DirichletCharacter ℂ q,
          ‖gaussSum χ⁻¹ stdAddChar * χ (-1) * ∏ j : Fin 4, χ.LFunction (s j)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ χ : DirichletCharacter ℂ q,
          Real.sqrt q * ∏ j : Fin 4, ‖χ.LFunction (s j)‖ := by
        apply Finset.sum_le_sum
        intro χ _
        have hminus : ‖χ (-1)‖ = 1 := by
          simpa using χ.unit_norm_eq_one (-1 : (ZMod q)ˣ)
        rw [norm_mul,norm_mul,hminus,mul_one,norm_prod]
        exact mul_le_mul_of_nonneg_right (all_gaussSum_norm_le_sqrt q χ⁻¹)
          (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
      _ = _ := (Finset.mul_sum _ _ _).symm
  unfold gaussFourLTransform
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

theorem allDirichlet_gauss_fourL_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ _ : NeZero q,
      ∀ s : Fin 4 → ℂ, (∀ j, (s j).re ∈ Icc (1/2 : ℝ) (3/4)) →
      ∀ V : ℝ, 0 ≤ V → (∀ j, |(s j).im| ≤ V) →
      ‖gaussFourLTransform q s‖ ≤ C*(q : ℝ)^(1/2+ε)*(1+V)^20 := by
  obtain ⟨A,hA,hfour⟩ := allDirichlet_fourLProduct (ε := ε/2) (by linarith)
  obtain ⟨D,hD,hratio⟩ := modulus_totient_ratio_subpower (ε := ε/2) (by linarith)
  refine ⟨A*D,by positivity,?_⟩
  intro q hq s hs V hV ht
  have : NeZero q := hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have he : Real.sqrt (q : ℝ)*(q : ℝ)^(1+ε/2) =
      (q : ℝ)*(q : ℝ)^(1/2+ε/2) := by
    calc
      _ = (q : ℝ)^((1/2 : ℝ)+(1+ε/2)) := by
        rw [Real.sqrt_eq_rpow,← Real.rpow_add hqpos]
      _ = (q : ℝ)^((1 : ℝ)+(1/2+ε/2)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hqpos,Real.rpow_one]
  have hpow : (q : ℝ)^(ε/2)*(q : ℝ)^(1/2+ε/2) = (q : ℝ)^(1/2+ε) := by
    rw [← Real.rpow_add hqpos]
    congr 1
    ring
  calc
    _ ≤ (q.totient : ℝ)⁻¹*Real.sqrt q*
        (A*(q : ℝ)^(1+ε/2)*(1+V)^20) :=
      (gaussFourLTransform_norm_le q s).trans (by gcongr; exact hfour q hq s hs V hV ht)
    _ = A*((q : ℝ)/(q.totient : ℝ))*(q : ℝ)^(1/2+ε/2)*(1+V)^20 := by
      calc
        _ = A*(q.totient : ℝ)⁻¹*
            (Real.sqrt q*(q : ℝ)^(1+ε/2))*(1+V)^20 := by ring
        _ = _ := by rw [he]; ring
    _ ≤ A*(D*(q : ℝ)^(ε/2))*(q : ℝ)^(1/2+ε/2)*(1+V)^20 := by
      gcongr
      exact hratio q hq
    _ = _ := by rw [show A*(D*(q : ℝ)^(ε/2))*(q : ℝ)^(1/2+ε/2) =
      A*D*((q : ℝ)^(ε/2)*(q : ℝ)^(1/2+ε/2)) by ring,hpow]

end
end Sechstmoment.Source
