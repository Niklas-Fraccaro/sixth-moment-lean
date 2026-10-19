import Sechstmoment.Arithmetic.Euler.Convolution.PairEuler

/-! Identify the previously constructed global remainder with its canonical Euler coefficients. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace Sechstmoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section
open Classical

def restLocal (s : Fin 4 → ℂ) (p : Nat.Primes) : ℕ → ℕ → ℂ :=
  residueRest (primeRoot p.val (s 0)) (primeRoot p.val (s 1))
    (primeRoot p.val (s 2)) (primeRoot p.val (s 3)) (primeX p.val)

@[simp] theorem restLocal_base (s : Fin 4 → ℂ) (p : Nat.Primes) : restLocal s p 0 0 = 1 :=
  residueRest_constant _ _ _ _ _

theorem restLocal_support (s : Fin 4 → ℂ) (p : Nat.Primes) (h k : ℕ)
    (H : 3 ≤ h ∨ 3 ≤ k) : restLocal s p h k = 0 :=
  residueRest_support _ _ _ _ _ (primeRoot_ne_zero p.val p.property.ne_zero (s 0)) h k H

theorem degree_pair_surjective (h k : ℕ) (hh : h ≤ 2) (hk : k ≤ 2)
    (h0 : h ≠ 0 ∨ k ≠ 0) : ∃ j : Fin 8, leftDegree j = h ∧ rightDegree j = k := by
  interval_cases h <;> interval_cases k
  · simp at h0
  all_goals decide

theorem pair_in_config_range (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (H : ∀ p ∈ primeSupport m ∪ primeSupport n,
      m.factorization p.val ≤ 2 ∧ n.factorization p.val ≤ 2) :
    (m,n) ∈ Set.range configIndex := by
  let S := primeSupport m ∪ primeSupport n
  have hex : ∀ p : S, ∃ j : Fin 8,
      leftDegree j = m.factorization p.val.val ∧ rightDegree j = n.factorization p.val.val := by
    intro p
    apply degree_pair_surjective _ _ (H p.val p.property).1 (H p.val p.property).2
    rcases Finset.mem_union.mp p.property with hp | hp
    · exact Or.inl (Finsupp.mem_support_iff.mp ((mem_primeSupport m p.val).mp hp))
    · exact Or.inr (Finsupp.mem_support_iff.mp ((mem_primeSupport n p.val).mp hp))
  choose j hj using hex
  let c : Configuration := ⟨S,j⟩
  refine ⟨c, Prod.ext ?_ ?_⟩
  · change primeProduct S (fun p => leftDegree (j p)) = m
    rw [show (fun p => leftDegree (j p)) = (fun p : S => m.factorization p.val.val) from
      funext (fun p => (hj p).1)]
    exact primeProduct_factorization m hm S Finset.subset_union_left
  · change primeProduct S (fun p => rightDegree (j p)) = n
    rw [show (fun p => rightDegree (j p)) = (fun p : S => n.factorization p.val.val) from
      funext (fun p => (hj p).2)]
    exact primeProduct_factorization n hn S Finset.subset_union_right

theorem pairEuler_config (s : Fin 4 → ℂ) (c : Configuration) :
    pairEuler (restLocal s) (configLeft c) (configRight c) = configCoeff s c := by
  rw [pairEuler_ambient _ (restLocal_base s) _ _ (configLeft_pos c).ne'
    (configRight_pos c).ne' c.1 (primeProduct_support c.1 _) (primeProduct_support c.1 _)]
  rw [← Finset.prod_coe_sort]
  apply Finset.prod_congr rfl
  intro p _
  rw [(config_factorization_mem c p.val p.property).1,
    (config_factorization_mem c p.val p.property).2]
  rfl

/-- The old configuration-extension definition and the ordinary prime-factor definition agree. -/
theorem gamma_eq_pairEuler (s : Fin 4 → ℂ) (m n : ℕ) :
    gamma s (m,n) = pairEuler (restLocal s) m n := by
  by_cases hm : m = 0
  · subst m
    simp [gamma_zero_left]
  by_cases hn : n = 0
  · subst n
    simp [gamma_zero_right]
  by_cases hc : (m,n) ∈ Set.range configIndex
  · obtain ⟨c,hc⟩ := hc
    have hl : configLeft c = m := congrArg Prod.fst hc
    have hr : configRight c = n := congrArg Prod.snd hc
    calc
      gamma s (m,n) = configCoeff s c := by rw [← hc, gamma_config]
      _ = pairEuler (restLocal s) m n := by rw [← hl, ← hr]; exact (pairEuler_config s c).symm
  · rw [gamma_outside s (m,n) hc, pairEuler, ite_eq_right (by simp [hm,hn])]
    symm
    have H : ¬ ∀ p ∈ primeSupport m ∪ primeSupport n,
        m.factorization p.val ≤ 2 ∧ n.factorization p.val ≤ 2 :=
      fun H => hc (pair_in_config_range m n hm hn H)
    obtain ⟨p,hp⟩ := not_forall.mp H
    obtain ⟨hpm,hlarge⟩ := not_imp.mp hp
    exact Finset.prod_eq_zero hpm (restLocal_support s p _ _ (by omega))

end
end Sechstmoment.Source.NoDPGlobalConvolution
