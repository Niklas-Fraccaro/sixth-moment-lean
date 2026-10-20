import SixthMoment.Arithmetic.Euler.Remainder.Configurations

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace SixthMoment.Source.NoDPGlobalRest
open NoDPLocal NoDPResidues NoDPLocalClosure
open scoped BigOperators
noncomputable section

def pairWeight (ρ : ℝ) (n : ℕ × ℕ) : ℝ := ((n.1 * n.2 : ℕ) : ℝ) ^ ρ
def localMass (p : Nat.Primes) (s : Fin 4 → ℂ) (ρ : ℝ) : ℝ :=
  ∑ j : Fin 8, ‖localCoeff p s j‖ * primeScale p.val ρ ^ (leftDegree j + rightDegree j)
def configMass (s : Fin 4 → ℂ) (ρ : ℝ) (c : Configuration) : ℝ :=
  ‖configCoeff s c‖ * pairWeight ρ (configIndex c)
def globalBound (ρ : ℝ) : ℝ := Real.exp (∑' p : Nat.Primes, primeMajorant ρ p)

theorem localMass_eq (p : Nat.Primes) (s : Fin 4 → ℂ) (ρ : ℝ) :
    localMass p s ρ = primeErrorMass p.val s ρ := by
  have hi := primeRoot_ne_zero p.val p.property.ne_zero (s 0)
  rw [primeErrorMass, errorMass_explicit _ _ _ _ _ hi]
  simp [localMass, localCoeff, leftDegree, rightDegree, Fin.sum_univ_succ,
    residueRest_10 _ _ _ _ _ hi, residueRest_01 _ _ _ _ _ hi,
    residueRest_20 _ _ _ _ _ hi, residueRest_02 _ _ _ _ _ hi,
    residueRest_11 _ _ _ _ _ hi, residueRest_21 _ _ _ _ _ hi,
    residueRest_12 _ _ _ _ _ hi, residueRest_22 _ _ _ _ _ hi]
  ring

theorem localMass_nonneg (p : Nat.Primes) (s : Fin 4 → ℂ) (ρ : ℝ) :
    0 ≤ localMass p s ρ := by
  rw [localMass_eq]
  exact primeErrorMass_nonneg _ _ _

theorem localMass_summable (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    Summable (fun p : Nat.Primes => localMass p s ρ) := by
  simpa only [localMass_eq] using prime_error_mass_summable s ρ hρ0 hρ hs

theorem pairWeight_config (ρ : ℝ) (c : Configuration) :
    pairWeight ρ (configIndex c) =
      ∏ p : c.1, primeScale p.val.val ρ ^ (leftDegree (c.2 p) + rightDegree (c.2 p)) := by
  unfold pairWeight configIndex configLeft configRight
  simp only [Nat.cast_mul, Nat.cast_prod, Nat.cast_pow]
  rw [← Finset.prod_mul_distrib, ← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_add]
  unfold primeScale
  rw [← Real.rpow_natCast_mul (by positivity),
    mul_comm (↑(leftDegree (c.2 p) + rightDegree (c.2 p)) : ℝ) ρ,
    Real.rpow_mul_natCast (by positivity)]

theorem configMass_product (s : Fin 4 → ℂ) (ρ : ℝ) (c : Configuration) :
    configMass s ρ c = ∏ p : c.1,
      ‖localCoeff p.val s (c.2 p)‖ * primeScale p.val.val ρ ^
        (leftDegree (c.2 p) + rightDegree (c.2 p)) := by
  simp only [configMass, configCoeff, norm_prod, pairWeight_config, Finset.prod_mul_distrib]

theorem configMass_nonneg (s : Fin 4 → ℂ) (ρ : ℝ) (c : Configuration) :
    0 ≤ configMass s ρ c := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem configMass_sum (s : Fin 4 → ℂ) (ρ : ℝ) (S : Finset Nat.Primes) :
    (∑ f : S → Fin 8, configMass s ρ ⟨S,f⟩) = ∏ p ∈ S, localMass p s ρ := by
  simp only [configMass_product]
  calc
    _ = ∏ p : S, ∑ j : Fin 8, ‖localCoeff p.val s j‖ *
        primeScale p.val.val ρ ^ (leftDegree j + rightDegree j) :=
      (Fintype.prod_sum (fun p : S => fun j : Fin 8 => ‖localCoeff p.val s j‖ *
        primeScale p.val.val ρ ^ (leftDegree j + rightDegree j))).symm
    _ = _ := Finset.prod_coe_sort S (fun p => localMass p s ρ)

theorem configMass_summable (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    Summable (configMass s ρ) := by
  apply (summable_sigma_of_nonneg (configMass_nonneg s ρ)).mpr
  constructor
  · intro S
    exact Summable.of_finite
  · simpa only [tsum_fintype, configMass_sum] using
      summable_finsetProd_of_summable_nonneg (fun p => localMass_nonneg p s ρ)
        (localMass_summable s ρ hρ0 hρ hs)

theorem configMass_bound (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    (∑' c, configMass s ρ c) ≤ globalBound ρ := by
  rw [(configMass_summable s ρ hρ0 hρ hs).tsum_sigma]
  simp only [tsum_fintype, configMass_sum]
  apply Real.tsum_le_of_sum_le
  · intro S
    exact Finset.prod_nonneg (fun p _ => localMass_nonneg p s ρ)
  intro T
  calc
    _ ≤ ∑ S ∈ (T.biUnion id).powerset, ∏ p ∈ S, localMass p s ρ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro S hS
        exact Finset.mem_powerset.mpr (Finset.subset_biUnion_of_mem id hS)
      · intro S _ _
        exact Finset.prod_nonneg (fun p _ => localMass_nonneg p s ρ)
    _ = ∏ p ∈ T.biUnion id, (1 + localMass p s ρ) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (∑ p ∈ T.biUnion id, primeMajorant ρ p) := by
      calc
        _ ≤ ∏ p ∈ T.biUnion id, (1 + primeMajorant ρ p) := by
          apply Finset.prod_le_prod₀
          · intro p _
            exact add_nonneg zero_le_one (localMass_nonneg p s ρ)
          · intro p _
            apply add_le_add_right
            rw [localMass_eq]
            exact prime_error_mass_bound p.val p.property s ρ hρ0 hρ hs
        _ ≤ _ := Real.prod_one_add_le_exp_sum _ (fun p => primeMajorant_nonneg ρ p)
    _ ≤ globalBound ρ := Real.exp_le_exp.mpr
      ((primeMajorant_summable ρ hρ).sum_le_tsum _ (fun p _ => primeMajorant_nonneg ρ p))

theorem gamma_weighted_summable (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    Summable (fun n : ℕ × ℕ => ‖gamma s n‖ * pairWeight ρ n) := by
  apply (configIndex_injective.summable_iff (fun n hn => by rw [gamma_outside s n hn]; simp)).mp
  simp only [Function.comp_def, gamma_config]
  change Summable (configMass s ρ)
  exact configMass_summable s ρ hρ0 hρ hs

theorem gamma_weighted_bound (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) :
    (∑' n : ℕ × ℕ, ‖gamma s n‖ * pairWeight ρ n) ≤ globalBound ρ := by
  have H := configIndex_injective.tsum_eq
    (f := fun n : ℕ × ℕ => ‖gamma s n‖ * pairWeight ρ n)
    (Function.support_subset_iff'.mpr (fun n hn => by rw [gamma_outside s n hn]; simp))
  rw [← H]
  simpa only [gamma_config, configMass] using configMass_bound s ρ hρ0 hρ hs

end
end SixthMoment.Source.NoDPGlobalRest
