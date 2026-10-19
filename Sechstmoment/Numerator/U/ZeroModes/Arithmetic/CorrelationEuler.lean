import Mathlib.NumberTheory.EulerProduct.Basic
import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.PairShiftedBFactors

/-! Division-free Euler reconstruction for correlations with finitely many
exceptional prime coefficients. The local constant coefficients need not be
one and may vanish. -/

namespace Sechstmoment
open scoped BigOperators
open ArithmeticFunction Nat

noncomputable section
set_option maxHeartbeats 50000

/-- A finite-prime coefficient, including the constant local coefficient at
every prime of the selected set. -/
def finitePrimeCoefficient (c : ℕ → ℕ → ℂ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  ∏ p ∈ S, c p (n.factorization p)

theorem finitePrimeCoefficient_pow_mul (c : ℕ → ℕ → ℂ)
    {S : Finset ℕ} {p : ℕ} (hp : p.Prime) (hpS : p ∉ S)
    (e : ℕ) (m : factoredNumbers S) :
    finitePrimeCoefficient c (insert p S) (p^e*m) =
      c p e * finitePrimeCoefficient c S m := by
  have hm0 : (m:ℕ) ≠ 0 := m.property.1
  have hpm : ¬ p ∣ (m:ℕ) := (hp.coprime_iff_not_dvd).mp
    (hp.factoredNumbers_coprime hpS m.property)
  rw [finitePrimeCoefficient, Finset.prod_insert hpS,
    factorization_mul (pow_ne_zero e hp.ne_zero) hm0]
  simp only [Finsupp.add_apply, factorization_pow_self hp,
    factorization_eq_zero_of_not_dvd hpm, add_zero]
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  have hqp : q ≠ p := by intro h; exact hpS (h ▸ hq)
  rw [hp.factorization_pow, Finsupp.single_apply, ite_eq_right hqp.symm, zero_add]

/-- A finite Euler product for arbitrary genuine local coefficients. In
particular this has no multiplicativity or nonvanishing assumption on the
function being reconstructed. -/
theorem finitePrimeCoefficient_hasSum (c : ℕ → ℕ → ℂ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (hc : ∀ p ∈ S, Summable (fun e : ℕ => ‖c p e‖)) :
    Summable (fun n : factoredNumbers S => ‖finitePrimeCoefficient c S n‖) ∧
      HasSum (fun n : factoredNumbers S => finitePrimeCoefficient c S n)
        (∏ p ∈ S, ∑' e : ℕ, c p e) := by
  induction S using Finset.induction with
  | empty =>
      rw [factoredNumbers_empty]
      simp only [finitePrimeCoefficient, Finset.prod_empty]
      exact ⟨(Set.finite_singleton 1).summable (fun _ => ‖(1:ℂ)‖),
        by convert hasSum_singleton 1 (fun _ : ℕ => (1:ℂ)) using 1; rfl⟩
  | @insert p S hpS ih =>
      have hp := hS p (Finset.mem_insert_self p S)
      have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      have hc' : ∀ q ∈ S, Summable (fun e : ℕ => ‖c q e‖) :=
        fun q hq => hc q (Finset.mem_insert_of_mem hq)
      have ih' := ih hS' hc'
      have hcp := hc p (Finset.mem_insert_self p S)
      constructor
      · rw [← (equivProdNatFactoredNumbers hp hpS).summable_iff]
        simp only [Function.comp_def, equivProdNatFactoredNumbers_apply',
          finitePrimeCoefficient_pow_mul c hp hpS, norm_mul]
        exact @Summable.mul_of_nonneg ℕ (factoredNumbers S)
          (fun e => ‖c p e‖) (fun n => ‖finitePrimeCoefficient c S n‖) hcp ih'.1
          (fun n : ℕ => norm_nonneg (c p n))
          (fun n : factoredNumbers S => norm_nonneg (finitePrimeCoefficient c S n))
      · rw [Finset.prod_insert hpS,
          ← (equivProdNatFactoredNumbers hp hpS).hasSum_iff]
        simp only [Function.comp_def, equivProdNatFactoredNumbers_apply',
          finitePrimeCoefficient_pow_mul c hp hpS]
        have hnorm : Summable (fun x : ℕ × factoredNumbers S =>
            ‖c p x.1 * finitePrimeCoefficient c S x.2‖) := by
          simpa only [norm_mul] using @Summable.mul_of_nonneg ℕ (factoredNumbers S)
            (fun e => ‖c p e‖) (fun n => ‖finitePrimeCoefficient c S n‖) hcp ih'.1
            (fun n : ℕ => norm_nonneg (c p n))
            (fun n : factoredNumbers S => norm_nonneg (finitePrimeCoefficient c S n))
        exact @HasSum.mul ℕ (factoredNumbers S) ℂ _ _ _ _
          (fun e => c p e) (fun n => finitePrimeCoefficient c S n)
          (∑' e : ℕ, c p e) (∏ q ∈ S, ∑' e : ℕ, c q e)
          hcp.of_norm.hasSum ih'.2 hnorm.of_norm

/-- The value of a multiplicative arithmetic function over any finite set
containing every prime divisor. Extra factors are its proved value at one. -/
theorem multiplicative_eq_finitePrimeCoefficient (f : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) {S : Finset ℕ} {n : ℕ}
    (hn : n ≠ 0) (hnS : n.primeFactors ⊆ S) :
    f n = finitePrimeCoefficient (fun p e => f (p^e)) S n := by
  rw [hf.multiplicative_factorization f hn]
  unfold Finsupp.prod finitePrimeCoefficient
  apply Finset.prod_subset
  · simpa only [Nat.support_factorization] using hnS
  · intro p _ hp
    have he : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp
    simp only [he, pow_zero, hf.map_one]

/-- Correlation reconstruction is a consequence of genuine prime
factorization, with every exponent of the two amplifier integers retained. -/
theorem arithmeticCorrelation_eq_finitePrimeCoefficient
    (f g w : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) (hw : w.IsMultiplicative)
    {a b n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hn : n ≠ 0)
    {S : Finset ℕ} (haS : a.primeFactors ⊆ S)
    (hbS : b.primeFactors ⊆ S) (hnS : n.primeFactors ⊆ S) :
    f (b*n)*g (a*n)*w n = finitePrimeCoefficient
      (fun p e => f (p^(b.factorization p+e))*
        g (p^(a.factorization p+e))*w (p^e)) S n := by
  rw [multiplicative_eq_finitePrimeCoefficient f hf (S:=S) (mul_ne_zero hb hn)
      (by rw [Nat.primeFactors_mul hb hn]; exact Finset.union_subset hbS hnS),
    multiplicative_eq_finitePrimeCoefficient g hg (S:=S) (mul_ne_zero ha hn)
      (by rw [Nat.primeFactors_mul ha hn]; exact Finset.union_subset haS hnS),
    multiplicative_eq_finitePrimeCoefficient w hw (S:=S) hn hnS]
  simp only [finitePrimeCoefficient, Nat.factorization_mul hb hn,
    Nat.factorization_mul ha hn, Finsupp.add_apply, Finset.prod_mul_distrib]

/-- A global Euler product whose finitely many exceptional local constants
can be arbitrary, including zero. The finite reconstruction hypothesis is
intended to be discharged by prime factorization, as above. -/
theorem finiteExceptionalEuler_hasProd (F : ℕ → ℂ) (c : ℕ → ℕ → ℂ)
    (E : Finset ℕ) (hE : ∀ p ∈ E, p.Prime)
    (hc : ∀ p, p.Prime → Summable (fun e : ℕ => ‖c p e‖))
    (hF : Summable (fun n : ℕ => ‖F n‖)) (hF0 : F 0 = 0)
    (hfactor : ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → E ⊆ S →
      ∀ n : factoredNumbers S, F n = finitePrimeCoefficient c S n) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ, c p e) (∑' n : ℕ, F n) := by
  let L : ℕ → ℂ := fun p => ∑' e : ℕ, c p e
  change HasProd (L ∘ Subtype.val (p := (· ∈ {x | Nat.Prime x}))) _
  rw [hasProd_subtype_iff_mulIndicator, HasProd, SummationFilter.unconditional,
    Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := EulerProduct.norm_tsum_factoredNumbers_sub_tsum_lt
    hF.of_norm hF0 hε
  refine ⟨Finset.range N ∪ E, fun S hS => ?_⟩
  have hES : E ⊆ {p ∈ S | p.Prime} := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨hS (Finset.mem_union_right _ hp), hE p hp⟩
  have hpS : ∀ p ∈ {p ∈ S | p.Prime}, p.Prime :=
    fun _ hp => (Finset.mem_filter.mp hp).2
  have hsum := (finitePrimeCoefficient_hasSum c {p ∈ S | p.Prime}
    hpS (fun p hp => hc p (hpS p hp))).2
  have hprod : ∏ p ∈ S, {p | Nat.Prime p}.mulIndicator L p =
      ∏ p ∈ S with p.Prime, L p :=
    Finset.prod_mulIndicator_eq_prod_filter S (fun _ => L) _ id
  rw [hprod, dist_eq_norm, hsum.tsum_eq.symm]
  have heq : (∑' n : factoredNumbers {p ∈ S | p.Prime},
      finitePrimeCoefficient c {p ∈ S | p.Prime} n) =
      ∑' n : factoredNumbers {p ∈ S | p.Prime}, F n := by
    apply tsum_congr
    intro n
    exact (hfactor _ hpS hES n).symm
  rw [heq, norm_sub_rev]
  apply hN
  intro p hp
  exact Finset.mem_filter.mpr
    ⟨hS (Finset.mem_union_left _ (Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp))),
      Nat.prime_of_mem_primesBelow hp⟩

/-- The global product for a fixed pair of amplifier integers is proved
without dividing by the initial correlation coefficient. -/
theorem arithmeticCorrelation_euler_hasProd
    (f g w : ArithmeticFunction ℂ)
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) (hw : w.IsMultiplicative)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : ∀ p, p.Prime → Summable (fun e : ℕ =>
      ‖f (p^(b.factorization p+e))*g (p^(a.factorization p+e))*w (p^e)‖))
    (hF : Summable (fun n : ℕ => ‖f (b*n)*g (a*n)*w n‖)) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ,
      f (p.val^(b.factorization p.val+e))*
        g (p.val^(a.factorization p.val+e))*w (p.val^e))
      (∑' n : ℕ, f (b*n)*g (a*n)*w n) := by
  apply finiteExceptionalEuler_hasProd _ _ (a.primeFactors ∪ b.primeFactors)
    (fun p hp => by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact Nat.prime_of_mem_primeFactors hp
      · exact Nat.prime_of_mem_primeFactors hp)
    hc hF (by simp)
  intro S _ hES n
  exact arithmeticCorrelation_eq_finitePrimeCoefficient f g w hf hg hw ha hb n.property.1
    (fun p hp => hES (Finset.mem_union_left _ hp))
    (fun p hp => hES (Finset.mem_union_right _ hp))
    (Nat.primeFactors_subset_of_mem_factoredNumbers n.property)

/-- The actual fixed-amplifier local coefficient series. -/
def shiftedPairCorrelationLocalSeries (p : ℕ) (α β γ δ : ℂ) (a b : ℕ) : ℂ :=
  ∑' j : ℕ, shiftedPairArithmetic α β (p^(b.factorization p+j))*
    shiftedPairArithmetic γ δ (p^(a.factorization p+j))*(1/(p:ℂ))^j

theorem coprime_prime_factorization_zero {a b p : ℕ} (hab : a.Coprime b)
    (hp : p.Prime) : a.factorization p=0 ∨ b.factorization p=0 := by
  by_cases hpa : p ∣ a
  · right
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpb
    exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpa hpb hab
  · exact Or.inl (Nat.factorization_eq_zero_of_not_dvd hpa)

theorem shiftedPairCorrelation_local_norm_summable
    {p a b : ℕ} (hp : p.Prime) (hab : a.Coprime b)
    (α β γ δ : ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hα : ‖(p:ℂ)^(-α)‖ ≤ M) (hβ : ‖(p:ℂ)^(-β)‖ ≤ M)
    (hγ : ‖(p:ℂ)^(-γ)‖ ≤ M) (hδ : ‖(p:ℂ)^(-δ)‖ ≤ M)
    (hr : M^2*‖1/(p:ℂ)‖ < 1) :
    Summable (fun j : ℕ => ‖shiftedPairArithmetic α β (p^(b.factorization p+j))*
      shiftedPairArithmetic γ δ (p^(a.factorization p+j))*
        shiftedPowerArithmetic 1 (p^j)‖) := by
  simp_rw [shiftedPairArithmetic_primePower hp, shiftedPowerArithmetic_primePower hp,
    Complex.cpow_neg_one]
  rcases coprime_prime_factorization_zero hab hp with ha0 | hb0
  · rw [ha0]
    simp only [zero_add]
    have hs := pairShiftedPrimeSeries_norm_summable hM hγ hδ hα hβ hr
      (b.factorization p)
    apply hs.congr
    intro j
    rw [Nat.add_comm (b.factorization p) j]
    congr 1
    ring
  · rw [hb0]
    simp only [zero_add]
    simpa only [Nat.add_comm, one_div] using
      pairShiftedPrimeSeries_norm_summable hM hα hβ hγ hδ hr (a.factorization p)

private theorem positiveShift_primeWeight_bound {e : ℝ} {p : ℕ}
    (hp : p.Prime) (z : ℂ) (hz : e ≤ z.re) :
    ‖(p:ℂ)^(-z)‖ ≤ (p:ℝ)^(-e) := by
  apply bblrPrimePowerNorm_le hp
  simp only [Complex.neg_re]
  linarith

private theorem positiveShift_primeRadius {e : ℝ} (he : 0 < e) (p : Nat.Primes) :
    ((p.val:ℝ)^(-e))^2*‖1/(p.val:ℂ)‖ < 1 := by
  rw [primePolarGeometricRadius p (-e)]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.property.one_lt) (by linarith)

/-- Euler reconstruction of the genuine translated two-shift coefficients
in a positive real-shift half-plane. Both global and local absolute
convergence are established from coefficient bounds. -/
theorem shiftedPairCorrelation_euler_hasProd {e : ℝ} (he : 0 < e)
    (α β γ δ : ℂ) (hα : e ≤ α.re) (hβ : e ≤ β.re)
    (hγ : e ≤ γ.re) (hδ : e ≤ δ.re)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    HasProd (fun p : Nat.Primes => shiftedPairCorrelationLocalSeries p.val α β γ δ a b)
      (∑' n : ℕ, shiftedPairArithmetic α β (b*n)*
        shiftedPairArithmetic γ δ (a*n)*shiftedPowerArithmetic 1 n) := by
  have hc (p : ℕ) (hp : p.Prime) := shiftedPairCorrelation_local_norm_summable
    hp hab α β γ δ (M:=(p:ℝ)^(-e)) (Real.rpow_nonneg (by positivity) _)
    (positiveShift_primeWeight_bound hp α hα) (positiveShift_primeWeight_bound hp β hβ)
    (positiveShift_primeWeight_bound hp γ hγ) (positiveShift_primeWeight_bound hp δ hδ)
    (positiveShift_primeRadius he ⟨p,hp⟩)
  have H := arithmeticCorrelation_euler_hasProd
    (shiftedPairArithmetic α β) (shiftedPairArithmetic γ δ) (shiftedPowerArithmetic 1)
    (shiftedPairArithmetic_multiplicative α β) (shiftedPairArithmetic_multiplicative γ δ)
    (shiftedPowerArithmetic_multiplicative 1) ha hb hc
    (shiftedPairCorrelation_norm_summable he α β γ δ hα hβ hγ hδ ha hb)
  apply H.congr_fun
  intro p
  unfold shiftedPairCorrelationLocalSeries
  simp_rw [shiftedPowerArithmetic_primePower p.property, Complex.cpow_neg_one, one_div]

theorem bblrBPrimeFactor_zero {p : ℕ} (hp : p.Prime)
    (α β γ δ : ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hα : ‖(p:ℂ)^(-α)‖ ≤ M) (hβ : ‖(p:ℂ)^(-β)‖ ≤ M)
    (hγ : ‖(p:ℂ)^(-γ)‖ ≤ M) (hδ : ‖(p:ℂ)^(-δ)‖ ≤ M)
    (hr : M^2*‖1/(p:ℂ)‖ < 1) : bblrBPrimeFactor p α β γ δ 0 = 1 := by
  rw [bblrBPrimeFactor_eq_pairSeries hp]
  change pairDiagonalPrimeSeries _ _ _ _ _ / pairDiagonalPrimeSeries _ _ _ _ _ = 1
  exact div_self (pairDiagonalPrimeSeries_ne_zero hM hα hβ hγ hδ hr)

/-- At a coprime amplifier pair the genuine local correlation has one
shifted prime exponent and one unshifted exponent. The resulting identity
does not require either numerator or either finite correction to be nonzero. -/
theorem shiftedPairCorrelationLocalSeries_eq_diagonal_mul_B
    {p a b : ℕ} (hp : p.Prime) (hab : a.Coprime b)
    (α β γ δ : ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hα : ‖(p:ℂ)^(-α)‖ ≤ M) (hβ : ‖(p:ℂ)^(-β)‖ ≤ M)
    (hγ : ‖(p:ℂ)^(-γ)‖ ≤ M) (hδ : ‖(p:ℂ)^(-δ)‖ ≤ M)
    (hr : M^2*‖1/(p:ℂ)‖ < 1) :
    shiftedPairCorrelationLocalSeries p α β γ δ a b =
      pairDiagonalPrimeSeries ((p:ℂ)^(-α)) ((p:ℂ)^(-β))
        ((p:ℂ)^(-γ)) ((p:ℂ)^(-δ)) (1/(p:ℂ))*
      bblrBPrimeFactor p α β γ δ (a.factorization p)*
      bblrBPrimeFactor p γ δ α β (b.factorization p) := by
  let D := ∑' j : ℕ, shiftedPairArithmetic α β (p^j)*
    shiftedPairArithmetic γ δ (p^j)*(1/(p:ℂ))^j
  have hD : D = pairDiagonalPrimeSeries ((p:ℂ)^(-α)) ((p:ℂ)^(-β))
      ((p:ℂ)^(-γ)) ((p:ℂ)^(-δ)) (1/(p:ℂ)) := by
    unfold D pairDiagonalPrimeSeries
    simp_rw [shiftedPairArithmetic_primePower hp]
  have hD0 : D ≠ 0 := hD ▸ pairDiagonalPrimeSeries_ne_zero hM hα hβ hγ hδ hr
  have hswap : (∑' j : ℕ, shiftedPairArithmetic γ δ (p^j)*
      shiftedPairArithmetic α β (p^j)*(1/(p:ℂ))^j) = D := by
    apply tsum_congr
    intro j
    ring
  have hα0 := bblrBPrimeFactor_zero hp α β γ δ hM hα hβ hγ hδ hr
  have hγ0 := bblrBPrimeFactor_zero hp γ δ α β hM hγ hδ hα hβ hr
  rw [← hD]
  rcases coprime_prime_factorization_zero hab hp with ha0 | hb0
  · rw [ha0, hα0, mul_one]
    have he : bblrBPrimeFactor p γ δ α β (b.factorization p) =
        shiftedPairCorrelationLocalSeries p α β γ δ a b / D := by
      unfold bblrBPrimeFactor
      rw [hswap]
      congr 1
      unfold shiftedPairCorrelationLocalSeries
      apply tsum_congr
      intro j
      rw [ha0, zero_add, Nat.add_comm (b.factorization p) j]
      ring
    rw [he]
    field_simp
  · rw [hb0, hγ0, mul_one]
    have he : bblrBPrimeFactor p α β γ δ (a.factorization p) =
        shiftedPairCorrelationLocalSeries p α β γ δ a b / D := by
      unfold bblrBPrimeFactor D shiftedPairCorrelationLocalSeries
      simp only [hb0, zero_add, Nat.add_comm (a.factorization p)]
    rw [he]
    field_simp

theorem bblrBFactor_positiveShift_hasProd {e : ℝ} (he : 0 < e)
    (α β γ δ : ℂ) (hα : e ≤ α.re) (hβ : e ≤ β.re)
    (hγ : e ≤ γ.re) (hδ : e ≤ δ.re) (a : ℕ) :
    HasProd (fun p : Nat.Primes => bblrBPrimeFactor p.val α β γ δ (a.factorization p.val))
      (bblrBFactor α β γ δ a) := by
  classical
  have h := hasProd_prod_of_ne_finset_one
    (L:=SummationFilter.unconditional Nat.Primes)
    (s:=a.primeFactors.subtype Nat.Prime)
    (f:=fun p : Nat.Primes => bblrBPrimeFactor p.val α β γ δ (a.factorization p.val))
    (fun p hp => by
      have hp' : p.val ∉ a.primeFactors := by
        intro hpv
        exact hp (Finset.mem_subtype.mpr hpv)
      have hν : a.factorization p.val=0 :=
        Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hp')
      rw [hν]
      exact bblrBPrimeFactor_zero p.property α β γ δ
        (Real.rpow_nonneg (by positivity) _)
        (positiveShift_primeWeight_bound p.property α hα)
        (positiveShift_primeWeight_bound p.property β hβ)
        (positiveShift_primeWeight_bound p.property γ hγ)
        (positiveShift_primeWeight_bound p.property δ hδ)
        (positiveShift_primeRadius he p))
  have hprod : (∏ p ∈ a.primeFactors.subtype Nat.Prime,
      bblrBPrimeFactor p.val α β γ δ (a.factorization p.val)) = bblrBFactor α β γ δ a := by
    rw [Finset.prod_subtype_of_mem
      (fun p => bblrBPrimeFactor p α β γ δ (a.factorization p))
      (fun p hp => Nat.prime_of_mem_primeFactors hp)]
    simp only [bblrBFactor, Finsupp.prod, Nat.support_factorization]
  exact hprod ▸ h

/-- The fixed coprime amplifier correlation equals the four-zeta diagonal
times its two literal finite `B` products. This is derived from the actual
Dirichlet coefficients and convergent products. -/
theorem shiftedPairCorrelation_eq_fourZeta_mul_B {e : ℝ} (he : 0 < e)
    (α β γ δ : ℂ) (hα : e ≤ α.re) (hβ : e ≤ β.re)
    (hγ : e ≤ γ.re) (hδ : e ≤ δ.re)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    (∑' n : ℕ, shiftedPairArithmetic α β (b*n)*
      shiftedPairArithmetic γ δ (a*n)*shiftedPowerArithmetic 1 n) =
      bblrAArithmetic α β γ δ * bblrBFactor α β γ δ a * bblrBFactor γ δ α β b := by
  have h := ((shiftedPairDiagonalPrimeSeries_zeta_hasProd he α β γ δ hα hβ hγ hδ).mul
    (bblrBFactor_positiveShift_hasProd he α β γ δ hα hβ hγ hδ a)).mul
    (bblrBFactor_positiveShift_hasProd he γ δ α β hγ hδ hα hβ b)
  have h' : HasProd
      (fun p : Nat.Primes => shiftedPairCorrelationLocalSeries p.val α β γ δ a b)
      (bblrAArithmetic α β γ δ * bblrBFactor α β γ δ a * bblrBFactor γ δ α β b) := by
    apply h.congr_fun
    intro p
    exact shiftedPairCorrelationLocalSeries_eq_diagonal_mul_B p.property hab α β γ δ
      (Real.rpow_nonneg (by positivity) _)
      (positiveShift_primeWeight_bound p.property α hα)
      (positiveShift_primeWeight_bound p.property β hβ)
      (positiveShift_primeWeight_bound p.property γ hγ)
      (positiveShift_primeWeight_bound p.property δ hδ)
      (positiveShift_primeRadius he p)
  exact (shiftedPairCorrelation_euler_hasProd he α β γ δ hα hβ hγ hδ ha hb hab).unique h'

/-- The literal `s`-dependent fixed-correlation identity. The two finite
products use the original coefficients and the power `p^{-j(1+2s)}`. -/
theorem shiftedPairCorrelationAt_eq_fourZeta_mul_B {e : ℝ} (he : 0 < e)
    (α β γ δ s : ℂ) (hα : e ≤ (α+s).re) (hβ : e ≤ (β+s).re)
    (hγ : e ≤ (γ+s).re) (hδ : e ≤ (δ+s).re)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    (∑' n : ℕ, shiftedPairArithmetic α β (b*n)*
      shiftedPairArithmetic γ δ (a*n)*shiftedPowerArithmetic (1+2*s) n) =
      bblrAArithmetic (α+s) (β+s) (γ+s) (δ+s) *
        bblrBFactorAt α β γ δ s a * bblrBFactorAt γ δ α β s b := by
  have H := shiftedPairCorrelation_eq_fourZeta_mul_B he
    (α+s) (β+s) (γ+s) (δ+s) hα hβ hγ hδ ha hb hab
  rw [shiftedPairCorrelation_add_shifts α β γ δ s ha hb,
    bblrBFactor_add_shifts α β γ δ s ha,
    bblrBFactor_add_shifts γ δ α β s hb] at H
  have hnonzero : (((a*b:ℕ):ℂ)^(-s)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr (mul_ne_zero ha hb)))
  apply mul_left_cancel₀ hnonzero
  rw [H, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

/-- BBLR's original compact shift domain and its initial integration
half-plane imply the literal fixed-correlation Euler identity. -/
theorem shiftedPairCorrelation_initial_eq_fourZeta_mul_BAt {α : MomentShifts}
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ 1/8) {s : ℂ} (hs : 1/4 ≤ s.re)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a.Coprime b) :
    (∑' n : ℕ, shiftedPairArithmetic (α 0) (α 1) (b*n)*
      shiftedPairArithmetic (α 2) (α 3) (a*n)*shiftedPowerArithmetic (1+2*s) n) =
      bblrAArithmetic (α 0+s) (α 1+s) (α 2+s) (α 3+s) *
        bblrBFactorAt (α 0) (α 1) (α 2) (α 3) s a *
        bblrBFactorAt (α 2) (α 3) (α 0) (α 1) s b := by
  have hre (j : Fin 4) : (1/8:ℝ) ≤ (α j+s).re := by
    have hj := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
    simp only [Complex.add_re]
    linarith
  exact shiftedPairCorrelationAt_eq_fourZeta_mul_B (by norm_num : (0:ℝ)<1/8)
    _ _ _ _ _ (hre 0) (hre 1) (hre 2) (hre 3) ha hb hab

end
end Sechstmoment
