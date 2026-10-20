import SixthMoment.Numerator.V.EulerTransfer.ProfileError
import SixthMoment.Numerator.V.Profiles.OriginalProfile


namespace SixthMoment.Source.NoDPGlobalLFactorization
open NoDPHarmonic NoDPGlobalConvolution Real Complex Polynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem sum_divisors_square_reindex (M : ℕ) (F : ℕ → ℕ → ℂ)
    (hleft : ∀ a b, M < a → F a b = 0)
    (hright : ∀ a b, M < b → F a b = 0) :
    (∑ N ∈ Finset.Icc 1 (M^2), ∑ d ∈ N.divisors, F d (N/d)) =
      ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, F a b := by
  classical
  have hM : M ≤ M^2 := by
    by_cases h0 : M = 0
    · simp [h0]
    · have h1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr h0
      nlinarith
  have hcut (a b : ℕ) (h : M^2 < a*b) : F a b = 0 := by
    by_cases ha : M < a
    · exact hleft a b ha
    · have hb : M < b := by
        by_contra hb
        exact (not_le_of_gt h) (by
          simpa only [pow_two] using Nat.mul_le_mul (le_of_not_gt ha) (le_of_not_gt hb))
      exact hright a b hb
  rw [sum_divisors_reindex (M^2) F hcut]
  calc
    _ = ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 (M^2), F a b := by
      symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hM)
      intro a ha hout
      have haM : M < a := by
        have ha1 := (Finset.mem_Icc.mp ha).1
        by_contra H
        exact hout (Finset.mem_Icc.mpr ⟨ha1,le_of_not_gt H⟩)
      exact Finset.sum_eq_zero (fun b _ => hleft a b haM)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      symm
      apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hM)
      intro b hb hout
      have hbM : M < b := by
        have hb1 := (Finset.mem_Icc.mp hb).1
        by_contra H
        exact hout (Finset.mem_Icc.mpr ⟨hb1,le_of_not_gt H⟩)
      exact hright a b hbM

theorem profileCoefficient_originalCoeff_reindex (M : ℕ) (L : ℝ)
    (f g : ℝ → ℂ) (i : Fin 4) (β : Fin 4 → ℂ)
    (hf : ∀ n : ℕ, M < n → f (Real.log n/L) = 0)
    (hg : ∀ n : ℕ, M < n → g (Real.log n/L) = 0) :
    (∑ N ∈ Finset.Icc 1 (M^2), profileCoefficient f g L N*originalCoeffAt i β N 1) =
      ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
        originalCoeffAt i β a b*f (Real.log a/L)*g (Real.log b/L) := by
  classical
  let F (a b : ℕ) := originalCoeffAt i β a b*f (Real.log a/L)*g (Real.log b/L)
  have hpoint (N : ℕ) : profileCoefficient f g L N*originalCoeffAt i β N 1 =
      ∑ d ∈ N.divisors, F d (N/d) := by
    rw [profileCoefficient,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have hc : originalCoeffAt i β N 1 = originalCoeffAt i β d (N/d) := by
      rw [originalCoeffAt_factor,originalCoeffAt_factor,
        Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd),mul_one]
    dsimp only [F]
    rw [hc]
    ring
  simp_rw [hpoint]
  exact sum_divisors_square_reindex M F
    (fun a b ha => by dsimp only [F]; rw [hf a ha,mul_zero,zero_mul])
    (fun a b hb => by dsimp only [F]; rw [hg b hb,mul_zero])

theorem profileCoefficient_eq_originalProfileSum {η L : ℝ} (hL : 0 < L)
    (i : Fin 4) (β : Fin 4 → ℂ) (P Q : ℝ[X]) :
    (∑ N ∈ Finset.Icc 1 (⌊Real.exp (L*η)⌋₊^2),
      profileCoefficient
        (fun x => (zeroExtendedPolynomialProfile η P x:ℂ))
        (fun x => (zeroExtendedPolynomialProfile η Q x:ℂ)) L N*originalCoeffAt i β N 1) =
      originalProfileSum η L i β P Q := by
  exact profileCoefficient_originalCoeff_reindex ⌊Real.exp (L*η)⌋₊ L _ _ i β
    (fun n hn => profileWeight_zero_of_lt hL P hn)
    (fun n hn => profileWeight_zero_of_lt hL Q hn)

end
end SixthMoment.Source.NoDPGlobalLFactorization
