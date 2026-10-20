import Sechstmoment.Numerator.V.EulerTransfer.DivisorRemainder

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open Complex Real MeasureTheory Filter Set ZMod
open scoped Topology BigOperators Classical ContDiff
noncomputable section

def profileCoefficient (f g : ℝ → ℂ) (L : ℝ) (N : ℕ) : ℂ :=
  ∑ d ∈ N.divisors, f (Real.log d / L) * g (Real.log (N/d:ℕ) / L)

theorem profileCoefficient_bound (f g : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ x, ‖f x‖ ≤ B) (hg : ∀ x, ‖g x‖ ≤ B) (L : ℝ) (N : ℕ) :
    ‖profileCoefficient f g L N‖ ≤ B^2 * N.divisors.card := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _d ∈ N.divisors, B^2 := by
      apply Finset.sum_le_sum
      intro d _
      rw [norm_mul,pow_two]
      exact mul_le_mul (hf _) (hg _) (norm_nonneg _) hB
    _ = _ := by simp [mul_comm]

theorem divisor_count_subpower (θ : ℝ) (hθ : 0 < θ) :
    ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, N ≠ 0 → (N.divisors.card:ℝ) ≤ D*(N:ℝ)^θ := by
  obtain ⟨D,hD,H⟩ := divisor_prime_cost_subpower (ε := θ) (C := 1) hθ (by norm_num)
  refine ⟨D+1,by positivity,?_⟩
  intro N hN
  have h := H N hN
  simp only [one_pow,mul_one] at h
  exact h.trans (by gcongr; linarith)

theorem positive_power_partial_sum (Y : ℕ) (hY : Y ≠ 0) (a : ℝ) (ha : 0 ≤ a) :
    (∑ N ∈ Finset.Icc 1 Y, (N:ℝ)^a) ≤ (Y:ℝ)^(a+1) := by
  have hYp : (0:ℝ) < Y := by exact_mod_cast Nat.pos_of_ne_zero hY
  calc
    _ ≤ ∑ _N ∈ Finset.Icc 1 Y, (Y:ℝ)^a := by
      apply Finset.sum_le_sum
      intro N hN
      exact Real.rpow_le_rpow (Nat.cast_nonneg N)
        (by exact_mod_cast (Finset.mem_Icc.mp hN).2) ha
    _ = (Y:ℝ)*(Y:ℝ)^a := by simp [nsmul_eq_mul]
    _ = _ := by
      calc
        _ = (Y:ℝ)^(1:ℝ)*(Y:ℝ)^a := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hYp];congr 1;ring

theorem positiveIndexNeZero (Y : ℕ) (N : Finset.Icc 1 Y) : N.val ≠ 0 :=
  Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp N.property).1

def profileRemainderSum (f g : ℝ → ℂ) (L : ℝ) (Y : ℕ) (w : ℝ → ℂ)
    (κ : ℝ) (s : Fin 4 → ℂ) (T : ℝ) : ℂ :=
  ∑ N : Finset.Icc 1 Y, profileCoefficient f g L N.val *
    displacedRemainder N.val (positiveIndexNeZero Y N) w κ s ((N.val:ℝ)*T)

theorem profileRemainderSum_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1:ℝ) 2) (κ ε θ : ℝ)
    (hκ : 1/2 < κ) (hε : 0 < ε) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f g : ℝ → ℂ, ∀ B : ℝ, 0 ≤ B →
      (∀ x, ‖f x‖ ≤ B) → (∀ x, ‖g x‖ ≤ B) → ∀ L : ℝ, ∀ Y : ℕ, Y ≠ 0 →
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ min κ (ε/2)) →
      (∀ j, κ+(s j).re ∈ Icc (1/2:ℝ) (3/4)) → ∀ T : ℝ, 0 < T →
      ‖profileRemainderSum f g L Y w κ s T‖ ≤
        C*B^2*T^κ*(Y:ℝ)^(κ+1/2+ε+θ) := by
  obtain ⟨A,hA,HA⟩ := displacedRemainder_scaled_bound hw hws κ ε hκ hε
  obtain ⟨D,hD,HD⟩ := divisor_count_subpower θ hθ
  refine ⟨A*D,by positivity,?_⟩
  intro f g B hB hf hg L Y hY s hs hsr T hT
  have hpoint (N : Finset.Icc 1 Y) :
      ‖profileCoefficient f g L N.val *
        displacedRemainder N.val (positiveIndexNeZero Y N) w κ s ((N.val:ℝ)*T)‖ ≤
      A*D*B^2*T^κ*(N.val:ℝ)^(κ-1/2+ε+θ) := by
    have hN := positiveIndexNeZero Y N
    have hNp : (0:ℝ) < N.val := by exact_mod_cast Nat.pos_of_ne_zero hN
    rw [norm_mul]
    calc
      _ ≤ (B^2*N.val.divisors.card) * (A*T^κ*(N.val:ℝ)^(κ-1/2+ε)) :=
        mul_le_mul (profileCoefficient_bound f g B hB hf hg L N.val)
          (HA N.val hN s hs hsr T hT) (norm_nonneg _) (by positivity)
      _ ≤ (B^2*(D*(N.val:ℝ)^θ)) * (A*T^κ*(N.val:ℝ)^(κ-1/2+ε)) := by
        gcongr
        exact HD N.val hN
      _ = _ := by
        calc
          _ = A*D*B^2*T^κ*((N.val:ℝ)^(κ-1/2+ε)*(N.val:ℝ)^θ) := by ring
          _ = _ := by rw [← Real.rpow_add hNp]
  have hsum : ‖profileRemainderSum f g L Y w κ s T‖ ≤
      ∑ N : Finset.Icc 1 Y, A*D*B^2*T^κ*(N.val:ℝ)^(κ-1/2+ε+θ) := by
    unfold profileRemainderSum
    exact (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun N _ => hpoint N))
  calc
    _ ≤ A*D*B^2*T^κ * ∑ N : Finset.Icc 1 Y, (N.val:ℝ)^(κ-1/2+ε+θ) := by
      simpa only [Finset.mul_sum] using hsum
    _ ≤ A*D*B^2*T^κ * (Y:ℝ)^((κ-1/2+ε+θ)+1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.sum_coe_sort (Finset.Icc 1 Y) (fun N : ℕ => (N:ℝ)^(κ-1/2+ε+θ))).le.trans
        (positive_power_partial_sum Y hY _ (by linarith))
    _ = _ := by congr 2;ring

end
end Sechstmoment.Source.NoDPGlobalLFactorization
