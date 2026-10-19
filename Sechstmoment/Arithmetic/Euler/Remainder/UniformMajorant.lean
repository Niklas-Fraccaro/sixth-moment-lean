import Sechstmoment.Arithmetic.Euler.Remainder.AbsoluteCoefficients

/-! A single summable coefficientwise majorant for the whole shift polydisc. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalRest
open NoDPLocal NoDPResidues NoDPLocalClosure
open scoped BigOperators
noncomputable section

def configMajorant (ρ : ℝ) (c : Configuration) : ℝ :=
  ∏ p : c.1, primeMajorant ρ p.val
def gammaMajorant (ρ : ℝ) : ℕ × ℕ → ℝ := Function.extend configIndex (configMajorant ρ) 0
def uniformBound (ρ : ℝ) : ℝ := Real.exp (8 * ∑' p : Nat.Primes, primeMajorant ρ p)

theorem localCoeff_bound (p : Nat.Primes) (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (j : Fin 8) :
    ‖localCoeff p s j‖ ≤ primeMajorant ρ p := by
  calc
    _ ≤ ‖localCoeff p s j‖ * primeScale p.val ρ ^ (leftDegree j + rightDegree j) :=
      le_mul_of_one_le_right (norm_nonneg _)
        (one_le_pow₀ (primeScale_one_le p.val p.property ρ hρ0))
    _ ≤ localMass p s ρ := by
      unfold localMass
      exact Finset.single_le_sum
        (f := fun k : Fin 8 => ‖localCoeff p s k‖ * primeScale p.val ρ ^
          (leftDegree k + rightDegree k))
        (fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p.val) ρ) _))
        (Finset.mem_univ j)
    _ ≤ primeMajorant ρ p := by
      rw [localMass_eq]
      exact prime_error_mass_bound p.val p.property s ρ hρ0 hρ hs

theorem configMajorant_nonneg (ρ : ℝ) (c : Configuration) : 0 ≤ configMajorant ρ c :=
  Finset.prod_nonneg (fun p _ => primeMajorant_nonneg ρ p.val)

theorem configCoeff_bound (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (c : Configuration) :
    ‖configCoeff s c‖ ≤ configMajorant ρ c := by
  unfold configCoeff configMajorant
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun p _ => localCoeff_bound p.val s ρ hρ0 hρ hs (c.2 p))

theorem configMajorant_sum (ρ : ℝ) (S : Finset Nat.Primes) :
    (∑ f : S → Fin 8, configMajorant ρ ⟨S,f⟩) =
      ∏ p ∈ S, (8 * primeMajorant ρ p) := by
  unfold configMajorant
  calc
    _ = ∏ p : S, ∑ _j : Fin 8, primeMajorant ρ p.val :=
      (Fintype.prod_sum (fun p : S => fun _ : Fin 8 => primeMajorant ρ p.val)).symm
    _ = ∏ p : S, 8 * primeMajorant ρ p.val := by simp
    _ = _ := Finset.prod_coe_sort S (fun p => 8 * primeMajorant ρ p)

theorem configMajorant_summable (ρ : ℝ) (hρ : ρ < 1/4) :
    Summable (configMajorant ρ) := by
  apply (summable_sigma_of_nonneg (configMajorant_nonneg ρ)).mpr
  constructor
  · intro S
    exact Summable.of_finite
  · simpa only [tsum_fintype, configMajorant_sum] using
      summable_finsetProd_of_summable_nonneg
        (fun p => mul_nonneg (by norm_num : (0:ℝ) ≤ 8) (primeMajorant_nonneg ρ p))
        ((primeMajorant_summable ρ hρ).mul_left 8)

theorem finsetProduct_tsum_bound {ι : Type*} (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hsa : Summable a) :
    (∑' S : Finset ι, ∏ i ∈ S, a i) ≤ Real.exp (∑' i, a i) := by
  classical
  apply Real.tsum_le_of_sum_le (fun S => Finset.prod_nonneg (fun i _ => ha i))
  intro T
  calc
    _ ≤ ∑ S ∈ (T.biUnion id).powerset, ∏ i ∈ S, a i :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun S hS => Finset.mem_powerset.mpr (Finset.subset_biUnion_of_mem id hS))
        (fun S _ _ => Finset.prod_nonneg (fun i _ => ha i))
    _ = ∏ i ∈ T.biUnion id, (1+a i) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (∑ i ∈ T.biUnion id, a i) := Real.prod_one_add_le_exp_sum _ ha
    _ ≤ Real.exp (∑' i, a i) := Real.exp_le_exp.mpr
      (hsa.sum_le_tsum _ (fun i _ => ha i))

theorem configMajorant_bound (ρ : ℝ) (hρ : ρ < 1/4) :
    (∑' c, configMajorant ρ c) ≤ uniformBound ρ := by
  rw [(configMajorant_summable ρ hρ).tsum_sigma]
  simp only [tsum_fintype, configMajorant_sum]
  simpa only [uniformBound, tsum_mul_left] using
    finsetProduct_tsum_bound (fun p => 8 * primeMajorant ρ p)
      (fun p => mul_nonneg (by norm_num) (primeMajorant_nonneg ρ p))
      ((primeMajorant_summable ρ hρ).mul_left 8)

theorem gammaMajorant_config (ρ : ℝ) (c : Configuration) :
    gammaMajorant ρ (configIndex c) = configMajorant ρ c :=
  configIndex_injective.extend_apply _ _ _

theorem gammaMajorant_outside (ρ : ℝ) (n : ℕ × ℕ) (hn : n ∉ Set.range configIndex) :
    gammaMajorant ρ n = 0 := Function.extend_apply' _ _ _ hn

theorem gammaMajorant_nonneg (ρ : ℝ) (n : ℕ × ℕ) : 0 ≤ gammaMajorant ρ n := by
  by_cases hn : n ∈ Set.range configIndex
  · obtain ⟨c, rfl⟩ := hn
    rw [gammaMajorant_config]
    exact configMajorant_nonneg ρ c
  · rw [gammaMajorant_outside ρ n hn]

theorem gammaMajorant_summable (ρ : ℝ) (hρ : ρ < 1/4) : Summable (gammaMajorant ρ) := by
  apply (configIndex_injective.summable_iff (gammaMajorant_outside ρ)).mp
  simp only [Function.comp_def, gammaMajorant_config]
  exact configMajorant_summable ρ hρ

theorem gammaMajorant_bound (ρ : ℝ) (hρ : ρ < 1/4) :
    (∑' n, gammaMajorant ρ n) ≤ uniformBound ρ := by
  rw [← configIndex_injective.tsum_eq (Function.support_subset_iff'.mpr (gammaMajorant_outside ρ))]
  simp only [gammaMajorant_config]
  exact configMajorant_bound ρ hρ

theorem gamma_norm_bound (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (n : ℕ × ℕ) :
    ‖gamma s n‖ ≤ gammaMajorant ρ n := by
  by_cases hn : n ∈ Set.range configIndex
  · obtain ⟨c, rfl⟩ := hn
    rw [gamma_config, gammaMajorant_config]
    exact configCoeff_bound s ρ hρ0 hρ hs c
  · rw [gamma_outside s n hn, gammaMajorant_outside ρ n hn, norm_zero]

theorem gamma_absolute (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    Summable (fun n => ‖gamma s n‖) :=
  (gammaMajorant_summable ρ hρ).of_nonneg_of_le (fun _ => norm_nonneg _)
    (gamma_norm_bound s ρ hρ0 hρ hs)

end
end Sechstmoment.Source.NoDPGlobalRest
