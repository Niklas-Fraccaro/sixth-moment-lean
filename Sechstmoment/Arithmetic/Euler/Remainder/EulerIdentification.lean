import Sechstmoment.Arithmetic.Euler.Remainder.AbsoluteCoefficients

/-! Identification of the absolutely convergent coefficient series with the remainder Euler product. -/
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalRest
open NoDPLocal NoDPResidues NoDPLocalClosure
open scoped BigOperators
noncomputable section

def localErrorEval (p : Nat.Primes) (s : Fin 4 → ℂ) (U V : ℂ) : ℂ :=
  ∑ j : Fin 8, localCoeff p s j * U ^ leftDegree j * V ^ rightDegree j

def configEval (s : Fin 4 → ℂ) (U V : Nat.Primes → ℂ) (c : Configuration) : ℂ :=
  ∏ p : c.1, localCoeff p.val s (c.2 p) * U p.val ^ leftDegree (c.2 p) *
    V p.val ^ rightDegree (c.2 p)

theorem localRest_eq_one_add (p : Nat.Primes) (s : Fin 4 → ℂ) (U V : ℂ) :
    primeRest p.val s U V = 1 + localErrorEval p s U V := by
  have hi := primeRoot_ne_zero p.val p.property.ne_zero (s 0)
  unfold primeRest restPolynomial localErrorEval
  simp [localCoeff, leftDegree, rightDegree, Fin.sum_univ_succ,
    residueRest_10 _ _ _ _ _ hi, residueRest_01 _ _ _ _ _ hi,
    residueRest_20 _ _ _ _ _ hi, residueRest_02 _ _ _ _ _ hi,
    residueRest_11 _ _ _ _ _ hi, residueRest_21 _ _ _ _ _ hi,
    residueRest_12 _ _ _ _ _ hi, residueRest_22 _ _ _ _ _ hi]
  ring

theorem configEval_norm_bound (s : Fin 4 → ℂ) (ρ : ℝ) (U V : Nat.Primes → ℂ)
    (hU : ∀ p, ‖U p‖ ≤ primeScale p.val ρ) (hV : ∀ p, ‖V p‖ ≤ primeScale p.val ρ)
    (c : Configuration) : ‖configEval s U V c‖ ≤ configMass s ρ c := by
  rw [configMass_product]
  unfold configEval
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro p _
  simp only [norm_mul, norm_pow, pow_add]
  rw [← mul_assoc]
  gcongr
  · exact mul_nonneg (norm_nonneg _) (pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p.val.val) ρ) _)
  · exact hU p.val
  · exact hV p.val

theorem configEval_absolute (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : Nat.Primes → ℂ)
    (hU : ∀ p, ‖U p‖ ≤ primeScale p.val ρ) (hV : ∀ p, ‖V p‖ ≤ primeScale p.val ρ) :
    Summable (fun c => ‖configEval s U V c‖) :=
  (configMass_summable s ρ hρ0 hρ hs).of_nonneg_of_le (fun _ => norm_nonneg _)
    (configEval_norm_bound s ρ U V hU hV)

theorem configEval_sum (s : Fin 4 → ℂ) (U V : Nat.Primes → ℂ) (S : Finset Nat.Primes) :
    (∑ f : S → Fin 8, configEval s U V ⟨S,f⟩) =
      ∏ p ∈ S, localErrorEval p s (U p) (V p) := by
  unfold configEval localErrorEval
  calc
    _ = ∏ p : S, ∑ j : Fin 8, localCoeff p.val s j *
        U p.val ^ leftDegree j * V p.val ^ rightDegree j :=
      (Fintype.prod_sum (fun p : S => fun j : Fin 8 => localCoeff p.val s j *
        U p.val ^ leftDegree j * V p.val ^ rightDegree j)).symm
    _ = _ := Finset.prod_coe_sort S (fun p => ∑ j : Fin 8,
      localCoeff p s j * U p ^ leftDegree j * V p ^ rightDegree j)

theorem restEuler_hasProd_configSum (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (U V : Nat.Primes → ℂ)
    (hU : ∀ p, ‖U p‖ ≤ primeScale p.val ρ) (hV : ∀ p, ‖V p‖ ≤ primeScale p.val ρ) :
    HasProd (fun p : Nat.Primes => primeRest p.val s (U p) (V p))
      (∑' c, configEval s U V c) := by
  have H := (configEval_absolute s ρ hρ0 hρ hs U V hU hV).of_norm
  have HE : (fun S : Finset Nat.Primes => ∑' f : S → Fin 8, configEval s U V ⟨S,f⟩) =
      (fun S => ∏ p ∈ S, localErrorEval p s (U p) (V p)) := by
    funext S
    rw [tsum_fintype, configEval_sum]
  have Hsum := H.hasSum.sigma (fun S => (Summable.of_finite).hasSum)
  rw [HE] at Hsum
  have HP := hasProd_one_add_of_hasSum_prod Hsum
  exact HP.congr_fun (fun p => localRest_eq_one_add p s (U p) (V p))

theorem nat_prod_cpow {ι : Type*} (T : Finset ι) (f : ι → ℕ) (z : ℂ) :
    ((∏ i ∈ T, f i : ℕ) : ℂ) ^ z = ∏ i ∈ T, (f i : ℂ) ^ z := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert i T hi ih =>
    simp only [Finset.prod_insert hi, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih]

theorem config_cpow (c : Configuration) (f : Fin 8 → ℕ) (z : ℂ) :
    ((∏ p : c.1, p.val.val ^ f (c.2 p) : ℕ) : ℂ) ^ z =
      ∏ p : c.1, ((p.val.val : ℂ) ^ z) ^ f (c.2 p) := by
  rw [nat_prod_cpow]
  apply Finset.prod_congr rfl
  intro p _
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, mul_comm,
    Complex.cpow_mul_nat]

def dirichletTerm (s : Fin 4 → ℂ) (u v : ℂ) (n : ℕ × ℕ) : ℂ :=
  gamma s n * (n.1 : ℂ)^(-u) * (n.2 : ℂ)^(-v)
def restDirichlet (s : Fin 4 → ℂ) (u v : ℂ) : ℂ := ∑' n, dirichletTerm s u v n

theorem dirichletTerm_config (s : Fin 4 → ℂ) (u v : ℂ) (c : Configuration) :
    dirichletTerm s u v (configIndex c) =
      configEval s (fun p => (p.val : ℂ)^(-u)) (fun p => (p.val : ℂ)^(-v)) c := by
  unfold dirichletTerm
  rw [gamma_config]
  simp only [configIndex, configLeft, configRight, config_cpow,
    configCoeff, configEval, Finset.prod_mul_distrib]

theorem dirichletTerm_outside (s : Fin 4 → ℂ) (u v : ℂ) (n : ℕ × ℕ)
    (hn : n ∉ Set.range configIndex) : dirichletTerm s u v n = 0 := by
  simp [dirichletTerm, gamma_outside s n hn]

theorem prime_cpow_bound (p : Nat.Primes) (z : ℂ) (ρ : ℝ) (hz : -ρ ≤ z.re) :
    ‖(p.val : ℂ)^(-z)‖ ≤ primeScale p.val ρ := by
  rw [Complex.norm_natCast_cpow_of_pos p.property.pos]
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_lt.le)
  simpa only [Complex.neg_re] using neg_le.mpr hz

theorem restDirichlet_absolute (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : -ρ ≤ u.re) (hv : -ρ ≤ v.re) :
    Summable (fun n => ‖dirichletTerm s u v n‖) := by
  apply (configIndex_injective.summable_iff
    (fun n hn => by rw [dirichletTerm_outside s u v n hn]; simp)).mp
  simpa only [Function.comp_def, dirichletTerm_config] using
    configEval_absolute s ρ hρ0 hρ hs _ _ (fun p => prime_cpow_bound p u ρ hu)
      (fun p => prime_cpow_bound p v ρ hv)

theorem restDirichlet_euler_hasProd (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : -ρ ≤ u.re) (hv : -ρ ≤ v.re) :
    HasProd (fun p : Nat.Primes => primeRest p.val s ((p.val : ℂ)^(-u)) ((p.val : ℂ)^(-v)))
      (restDirichlet s u v) := by
  have H := configIndex_injective.tsum_eq (Function.support_subset_iff'.mpr (dirichletTerm_outside s u v))
  simp only [dirichletTerm_config] at H
  rw [restDirichlet, ← H]
  exact restEuler_hasProd_configSum s ρ hρ0 hρ hs _ _
    (fun p => prime_cpow_bound p u ρ hu) (fun p => prime_cpow_bound p v ρ hv)

theorem restDirichlet_eq_euler (s : Fin 4 → ℂ) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : -ρ ≤ u.re) (hv : -ρ ≤ v.re) :
    restDirichlet s u v =
      ∏' p : Nat.Primes, primeRest p.val s ((p.val : ℂ)^(-u)) ((p.val : ℂ)^(-v)) :=
  (restDirichlet_euler_hasProd s ρ hρ0 hρ hs u v hu hv).tprod_eq.symm

def arithmeticConstant : ℂ := ∏' p : Nat.Primes,
  (1-primeX p.val)^4 * (1+4*primeX p.val+(primeX p.val)^2)

theorem zero_shift_global_factor : restDirichlet (fun _ => 0) 0 0 = arithmeticConstant := by
  rw [restDirichlet_eq_euler (fun _ => 0) 0 (by norm_num) (by norm_num)
    (by intro j; simp) 0 0 (by norm_num) (by norm_num)]
  simp only [neg_zero, Complex.cpow_zero, primeRest_zero_shifts, arithmeticConstant]

end
end Sechstmoment.Source.NoDPGlobalRest
