import Sechstmoment.Analysis.Fourier.ProfileProduct


namespace Sechstmoment.Source
open Complex Real Set
open scoped ContDiff BigOperators
noncomputable section

theorem compact_derivative_product_bound {Φ A : ℝ → ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) {a b T : ℝ} (hT : 1 ≤ T)
    (hs : tsupport Φ ⊆ Icc a b)
    (hA : ∀ x ∈ Icc a b, ContDiffAt ℝ ∞ A x)
    {C B : ℕ → ℝ} (hC : ∀ j, 0 ≤ C j) (hB : ∀ j, 0 ≤ B j)
    (hΦd : ∀ j x, ‖iteratedDeriv j Φ x‖ ≤ C j) (N : ℕ)
    (hAd : ∀ j, j ≤ N → ∀ x ∈ Icc a b, ‖iteratedDeriv j A x‖ ≤ B j*T^j)
    (x : ℝ) :
    ‖iteratedDeriv N (a03ProfileProduct Φ A) x‖ ≤
      a03ProfileProductDerivativeBudget C B N*T^N := by
  have hT0 : 0 ≤ T := by linarith
  have hbudget : 0 ≤ a03ProfileProductDerivativeBudget C B N := by
    unfold a03ProfileProductDerivativeBudget
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC i)) (hB _))
  by_cases hx : x ∈ tsupport Φ
  · have hxI := hs hx
    rw [show a03ProfileProduct Φ A = fun x => Φ x*A x from rfl,
      iteratedDeriv_fun_mul (hΦ.contDiffAt.of_le (by simp))
        ((hA x hxI).of_le (by simp))]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (N+1), (N.choose i:ℝ)*C i*(B (N-i)*T^N) := by
        apply Finset.sum_le_sum
        intro i _
        simp only [norm_mul,Complex.norm_natCast]
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hΦd i x) (Nat.cast_nonneg _)
        · exact (hAd (N-i) (Nat.sub_le _ _) x hxI).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (Nat.sub_le _ _)) (hB _))
        · exact norm_nonneg _
        · exact mul_nonneg (Nat.cast_nonneg _) (hC i)
      _ = _ := by
        unfold a03ProfileProductDerivativeBudget
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
  · have hz : iteratedDeriv N (a03ProfileProduct Φ A) x = 0 := by
      apply Function.notMem_support.mp
      intro hm
      exact hx (a03_profile_product_tsupport Φ A
        (a03_iteratedDeriv_tsupport_subset (a03ProfileProduct Φ A) N (subset_tsupport _ hm)))
    rw [hz,norm_zero]
    exact mul_nonneg hbudget (pow_nonneg hT0 N)

end
end Sechstmoment.Source
