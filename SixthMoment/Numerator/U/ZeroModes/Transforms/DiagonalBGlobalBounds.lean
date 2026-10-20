import SixthMoment.Numerator.U.ZeroModes.Transforms.DiagonalBContinuation


namespace SixthMoment
open Complex Real Nat Set
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03DiagonalBFactorRational (α β γ δ s : ℂ) (a : ℕ) : ℂ :=
  a.factorization.prod (fun p ν => a03DiagonalBPrimeRational p α β γ δ s ν)

theorem bblrBFactorAt_eq_rational (α β γ δ s : ℂ)
    (hα : ‖α‖≤1/64) (hβ : ‖β‖≤1/64) (hγ : ‖γ‖≤1/64) (hδ : ‖δ‖≤1/64)
    (hs : -(1/8:ℝ)≤s.re) (a : ℕ) :
    bblrBFactorAt α β γ δ s a=a03DiagonalBFactorRational α β γ δ s a := by
  unfold bblrBFactorAt a03DiagonalBFactorRational Finsupp.prod
  apply Finset.prod_congr rfl
  intro p hp
  exact bblrBPrimeFactorAt_eq_rational (Nat.prime_of_mem_primeFactors hp)
    α β γ δ s hα hβ hγ hδ hs _

theorem a03Factorization_rpow_prod {a : ℕ} (ha : a≠0) (ε : ℝ) :
    (∏ p∈a.primeFactors,((p:ℝ)^ε)^a.factorization p)=(a:ℝ)^ε := by
  have he (p : ℕ) : ((p:ℝ)^ε)^a.factorization p=((p:ℝ)^a.factorization p)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg p),
      ←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg p)]
    congr 1
    ring
  simp_rw [he]
  rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
  congr 1
  exact_mod_cast (Nat.prod_primeFactors_pow_factorization ha).symm

theorem bblrBFactorAt_norm_le_divisor_prime_cost (α β γ δ s : ℂ)
    (hα : ‖α‖≤1/64) (hβ : ‖β‖≤1/64) (hγ : ‖γ‖≤1/64) (hδ : ‖δ‖≤1/64)
    (hs : -(1/8:ℝ)≤s.re) {a : ℕ} (ha : a≠0) :
    ‖bblrBFactorAt α β γ δ s a‖≤
      (a.divisors.card:ℝ)*(8:ℝ)^a.primeFactors.card*(a:ℝ)^(1/64:ℝ) := by
  rw [bblrBFactorAt_eq_rational α β γ δ s hα hβ hγ hδ hs]
  unfold a03DiagonalBFactorRational Finsupp.prod
  rw [norm_prod]
  calc
    _≤∏ p∈a.primeFactors,8*(a.factorization p+1:ℝ)*
        ((p:ℝ)^(1/64:ℝ))^a.factorization p := by
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun p hp =>
        a03DiagonalBPrimeRational_norm_le (Nat.prime_of_mem_primeFactors hp)
          α β γ δ s hα hβ hγ hδ hs _)
    _=_ := by
      rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,Finset.prod_const,
        a03Factorization_rpow_prod ha,Nat.card_divisors ha,Nat.cast_prod]
      simp only [Nat.cast_add,Nat.cast_one]
      ring

theorem bblrBFactorAt_uniform_subpower_bound :
    ∃ D : ℝ,0≤D ∧ ∀ α β γ δ s : ℂ,∀ a : ℕ,a≠0 →
      ‖α‖≤1/64 → ‖β‖≤1/64 → ‖γ‖≤1/64 → ‖δ‖≤1/64 →
      -(1/8:ℝ)≤s.re → ‖bblrBFactorAt α β γ δ s a‖≤D*(a:ℝ)^(1/32:ℝ) := by
  obtain ⟨D,hD,hb⟩ := divisor_prime_cost_subpower (by norm_num : (0:ℝ)<1/64)
    (by norm_num : (1:ℝ)≤8)
  refine ⟨D,hD,?_⟩
  intro α β γ δ s a ha hα hβ hγ hδ hs
  calc
    _ ≤ (a.divisors.card:ℝ)*(8:ℝ)^a.primeFactors.card*(a:ℝ)^(1/64:ℝ) :=
      bblrBFactorAt_norm_le_divisor_prime_cost α β γ δ s hα hβ hγ hδ hs ha
    _ ≤ (D*(a:ℝ)^(1/64:ℝ))*(a:ℝ)^(1/64:ℝ) :=
      mul_le_mul_of_nonneg_right (hb a ha) (Real.rpow_nonneg (Nat.cast_nonneg a) _)
    _ = _ := by
      rw [mul_assoc,←Real.rpow_add (by exact_mod_cast Nat.pos_of_ne_zero ha)]
      congr 2
      norm_num

theorem a03DiagonalBPrimeRational_differentiableAt {p : ℕ} (hp : p.Prime)
    (α β γ δ : ℂ) (ν : ℕ) {s : ℂ}
    (hden : 1<(2+(α+β+γ+δ+4*s)).re) :
    DifferentiableAt ℂ (fun z => a03DiagonalBPrimeRational p α β γ δ z ν) s := by
  unfold a03DiagonalBPrimeRational a03DiagonalBPrimeCorrection bblrEtaCorrection
  apply DifferentiableAt.const_add
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.div
  · apply DifferentiableAt.mul
    all_goals apply DifferentiableAt.const_sub
    all_goals apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (Nat.cast_ne_zero.mpr hp.ne_zero)
    · fun_prop
    · exact Or.inl (Nat.cast_ne_zero.mpr hp.ne_zero)
  · apply DifferentiableAt.const_sub
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl (Nat.cast_ne_zero.mpr hp.ne_zero)
  · exact Complex.one_sub_prime_cpow_ne_zero hp hden

theorem a03DiagonalBFactorRational_differentiableAt (α β γ δ : ℂ) (a : ℕ) {s : ℂ}
    (hden : 1<(2+(α+β+γ+δ+4*s)).re) :
    DifferentiableAt ℂ (fun z => a03DiagonalBFactorRational α β γ δ z a) s := by
  unfold a03DiagonalBFactorRational Finsupp.prod
  apply DifferentiableAt.fun_finsetProd
  intro p hp
  exact a03DiagonalBPrimeRational_differentiableAt (Nat.prime_of_mem_primeFactors hp) α β γ δ _ hden

end
end SixthMoment
