import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-! A uniform subpower bound for a divisor count times a fixed cost at
every distinct prime. This supplies a genuine arithmetic majorant for
the two ratio-contour eta divisor sums. -/

namespace Sechstmoment
open Real Nat Finset Filter
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem nat_succ_le_geometric_majorant {q : ℝ} (hq : 1<q) (ν : ℕ) :
    (ν+1:ℝ)≤(q/(q-1))*q^ν := by
  have hs : (ν+1:ℝ)≤∑ j∈Finset.range (ν+1),q^j := by
    calc
      _ = ∑ _j∈Finset.range (ν+1),(1:ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun j _ => one_le_pow₀ hq.le)
  have hg := geom_sum_mul q (ν+1)
  have hb : (∑ j∈Finset.range (ν+1),q^j)≤q^(ν+1)/(q-1) := by
    apply (le_div_iff₀ (by linarith : 0<q-1)).mpr
    linarith
  apply hs.trans
  convert hb using 1
  rw [pow_succ]
  ring

theorem nat_succ_le_two_pow (ν : ℕ) : (ν+1:ℝ)≤(2:ℝ)^ν := by
  induction ν with
  | zero => norm_num
  | succ ν ih =>
      rw [pow_succ]
      push_cast
      nlinarith [one_le_pow₀ (by norm_num : (1:ℝ)≤2) (n := ν)]

/-- For every fixed prime cost `C`, the literal number of divisors times
`C` to the number of distinct primes is bounded by `D n^ε` uniformly in n.
No divisor-growth premise is used. -/
theorem divisor_prime_cost_subpower {ε C : ℝ} (hε : 0<ε) (hC : 1≤C) :
    ∃ D : ℝ,0≤D ∧ ∀ n : ℕ,n≠0 →
      (n.divisors.card:ℝ)*C^n.primeFactors.card≤D*(n:ℝ)^ε := by
  let q : ℝ := (2:ℝ)^ε
  have hq : 1<q := by
    dsimp [q]
    exact Real.one_lt_rpow (by norm_num) hε
  let E : ℝ := C*(q/(q-1))
  have hE : 1≤E := by
    have hf : 1≤q/(q-1) := (le_div_iff₀ (by linarith : 0<q-1)).mpr (by linarith)
    dsimp [E]
    nlinarith
  obtain ⟨P,hP⟩ := Filter.eventually_atTop.mp
    (((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (2*C)))
  refine ⟨E^P,by positivity,?_⟩
  intro n hn
  have hf (p : ℕ) (hp : p∈n.primeFactors) :
      ((n.factorization p+1:ℕ):ℝ)*C≤
        (if p<P then E else 1)*(p:ℝ)^(ε*(n.factorization p:ℝ)) := by
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hν : 1≤n.factorization p :=
      hp'.dvd_iff_one_le_factorization hn |>.mp (Nat.dvd_of_mem_primeFactors hp)
    have hqp : q≤(p:ℝ)^ε := by
      dsimp [q]
      exact Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hp'.two_le) hε.le
    by_cases hpP : p<P
    · rw [ite_eq_left hpP]
      have hnν := nat_succ_le_geometric_majorant hq (n.factorization p)
      have hνpow : q^(n.factorization p)≤(p:ℝ)^(ε*(n.factorization p:ℝ)) := by
        rw [Real.rpow_mul (by positivity : (0:ℝ)≤p),Real.rpow_natCast]
        exact pow_le_pow_left₀ (by positivity) hqp _
      calc
        _ ≤ ((q/(q-1))*q^(n.factorization p))*C :=
          mul_le_mul_of_nonneg_right (by simpa only [Nat.cast_add,Nat.cast_one] using hnν)
            (by linarith)
        _ = E*q^(n.factorization p) := by dsimp [E]; ring
        _ ≤ E*(p:ℝ)^(ε*(n.factorization p:ℝ)) :=
          mul_le_mul_of_nonneg_left hνpow (by linarith)
    · rw [ite_eq_right hpP,one_mul]
      have hCp : 2*C≤(p:ℝ)^ε := hP p (by omega)
      have hCpow : C≤C^(n.factorization p) := by
        simpa only [pow_one] using pow_le_pow_right₀ hC hν
      calc
        _ ≤ (2:ℝ)^(n.factorization p)*C^(n.factorization p) := by
          have hh := nat_succ_le_two_pow (n.factorization p)
          push_cast at hh ⊢
          exact mul_le_mul hh hCpow (by linarith) (by positivity)
        _ = (2*C)^(n.factorization p) := (mul_pow _ _ _).symm
        _ ≤ ((p:ℝ)^ε)^(n.factorization p) := pow_le_pow_left₀ (by linarith) hCp _
        _ = _ := by rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : (0:ℝ)≤p)]
  have hprod : (∏ p∈n.primeFactors,(p:ℝ)^(ε*(n.factorization p:ℝ)))=(n:ℝ)^ε := by
    have he (p : ℕ) : (p:ℝ)^(ε*(n.factorization p:ℝ))=
        ((p:ℝ)^(n.factorization p))^ε := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : (0:ℝ)≤p)]
      congr 1
      ring
    simp_rw [he]
    rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  have hcost : (∏ p∈n.primeFactors,if p<P then E else (1:ℝ))≤E^P := by
    rw [Finset.prod_ite,Finset.prod_const,Finset.prod_const,one_pow,mul_one]
    apply pow_le_pow_right₀ hE
    apply (Finset.card_le_card ?_).trans_eq (Finset.card_range P)
    intro p hp
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
  rw [Nat.card_divisors hn,Nat.cast_prod]
  calc
    _ = ∏ p∈n.primeFactors,((n.factorization p+1:ℕ):ℝ)*C := by
      rw [Finset.prod_mul_distrib,Finset.prod_const]
    _ ≤ ∏ p∈n.primeFactors,(if p<P then E else 1)*(p:ℝ)^(ε*(n.factorization p:ℝ)) := by
      exact Finset.prod_le_prod₀ (fun p _ => by positivity) hf
    _ = (∏ p∈n.primeFactors,if p<P then E else (1:ℝ))*(n:ℝ)^ε := by
      rw [Finset.prod_mul_distrib,hprod]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcost (by positivity)

end
end Sechstmoment

/-! A uniform subpower bound for a divisor count times a fixed cost at
every distinct prime. This supplies a genuine arithmetic majorant for
the two ratio-contour eta divisor sums. -/

namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Real Nat Finset Filter
open scoped BigOperators
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem nat_succ_le_geometric_majorant {q : ℝ} (hq : 1<q) (ν : ℕ) :
    (ν+1:ℝ)≤(q/(q-1))*q^ν :=
  @Sechstmoment.nat_succ_le_geometric_majorant q hq ν

theorem nat_succ_le_two_pow (ν : ℕ) : (ν+1:ℝ)≤(2:ℝ)^ν :=
  @Sechstmoment.nat_succ_le_two_pow ν

/-- For every fixed prime cost `C`, the literal number of divisors times
`C` to the number of distinct primes is bounded by `D n^ε` uniformly in n.
No divisor-growth premise is used. -/
theorem divisor_prime_cost_subpower {ε C : ℝ} (hε : 0<ε) (hC : 1≤C) :
    ∃ D : ℝ,0≤D ∧ ∀ n : ℕ,n≠0 →
      (n.divisors.card:ℝ)*C^n.primeFactors.card≤D*(n:ℝ)^ε :=
  @Sechstmoment.divisor_prime_cost_subpower ε C hε hC

end
end Sechstmoment.Source.NoDPGlobalLFactorization
