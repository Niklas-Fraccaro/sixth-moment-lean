import Sechstmoment.Numerator.V.Arithmetic.Additive.GCD

/-! The genuinely infinite additive character identity. Absolute
summability is recorded before the finite/infinite sums are exchanged.
The gcd fibres are reindexed by literal multiplication by the divisor.
-/

namespace Sechstmoment.Source
open Complex Real ZMod Finset
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 800000

def gcdCharacterSeries (N d : ℕ) (c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ (N/d)) : ℂ :=
  ∑' m : ℕ, if Nat.gcd m N = d then c m*χ (m/d) else 0

theorem gcd_character_terms_summable (N d : ℕ) (c : ℕ → ℂ)
    (hc : Summable c) (χ : DirichletCharacter ℂ (N/d)) :
    Summable (fun m : ℕ => if Nat.gcd m N = d then c m*χ (m/d) else 0) := by
  apply hc.norm.of_norm_bounded
  intro m
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (χ.norm_le_one _)
  · simp

theorem gcd_character_series_reindexed (N : ℕ) [NeZero N]
    (c : ℕ → ℂ) {d : ℕ} (hd : d ∈ N.divisors)
    (χ : DirichletCharacter ℂ (N/d)) :
    gcdCharacterSeries N d c χ = ∑' n : ℕ, c (d*n)*χ n := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdN := (Nat.mem_divisors.mp hd).1
  let f : ℕ → ℂ := fun m => if Nat.gcd m N = d then c m*χ (m/d) else 0
  have hinj : Function.Injective (fun n : ℕ => d*n) := by
    intro n m h
    exact Nat.eq_of_mul_eq_mul_left hdpos h
  have hsupp : Function.support f ⊆ Set.range (fun n : ℕ => d*n) := by
    intro m hm
    have he : Nat.gcd m N = d := by
      by_contra h
      exact hm (by simp [f,h])
    exact ⟨m/d,Nat.mul_div_cancel' (he ▸ Nat.gcd_dvd_left m N)⟩
  unfold gcdCharacterSeries
  change (∑' m : ℕ, f m) = _
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro n
  by_cases hcop : Nat.Coprime n (N/d)
  · have he : Nat.gcd (d*n) N = d := by
      rw [show N = d*(N/d) from (Nat.mul_div_cancel' hdN).symm,
        Nat.gcd_mul_left,hcop.gcd_eq_one,mul_one]
    simp [f,he,Nat.mul_div_cancel_left n hdpos]
  · have hne : Nat.gcd (d*n) N ≠ d := by
      intro he
      have h := additive_gcd_quotient_coprime
        (Nat.pos_of_ne_zero (NeZero.ne N)) he
      exact hcop (by simpa only [Nat.mul_div_cancel_left n hdpos] using h)
    have hunit : ¬ IsUnit (n : ZMod (N/d)) := by
      simpa only [ZMod.isUnit_iff_coprime] using hcop
    simp [f,hne,MulChar.map_nonunit _ hunit]

def gcdCharacterSeriesContribution (N d : ℕ) (c : ℕ → ℂ) : ℂ :=
  if hq : N/d = 0 then 0 else
    letI : NeZero (N/d) := ⟨hq⟩
    ((N/d).totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ (N/d),
      gaussSum χ⁻¹ stdAddChar * χ (-1) * gcdCharacterSeries N d c χ

theorem gcdCharacterContribution_tsum (N : ℕ) [NeZero N]
    (c : ℕ → ℂ) (hc : Summable c) {d : ℕ} (hd : d ∈ N.divisors) :
    (∑' m : ℕ, gcdCharacterContribution N d {m} c) =
      gcdCharacterSeriesContribution N d c := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hqpos : 0 < N/d := Nat.div_pos
    (Nat.le_of_dvd hNpos (Nat.mem_divisors.mp hd).1) hdpos
  have : NeZero (N/d) := ⟨hqpos.ne'⟩
  have he (χ : DirichletCharacter ℂ (N/d)) (m : ℕ) :
      gcdCharacterTransform N d {m} c χ =
        if Nat.gcd m N = d then c m*χ (m/d) else 0 := by
    simp [gcdCharacterTransform,additiveGCDFibre,Finset.sum_filter]
  simp only [gcdCharacterContribution,gcdCharacterSeriesContribution,dite_eq_right hqpos.ne']
  simp_rw [he]
  rw [tsum_mul_left,Summable.tsum_finsetSum]
  · simp only [gcdCharacterSeries,tsum_mul_left]
  · intro χ _
    exact (gcd_character_terms_summable N d c hc χ).mul_left _

theorem gcdCharacterContribution_summable (N : ℕ) [NeZero N]
    (c : ℕ → ℂ) (hc : Summable c) {d : ℕ} (hd : d ∈ N.divisors) :
    Summable (fun m : ℕ => gcdCharacterContribution N d {m} c) := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hqpos : 0 < N/d := Nat.div_pos
    (Nat.le_of_dvd hNpos (Nat.mem_divisors.mp hd).1) hdpos
  have : NeZero (N/d) := ⟨hqpos.ne'⟩
  have he (χ : DirichletCharacter ℂ (N/d)) (m : ℕ) :
      gcdCharacterTransform N d {m} c χ =
        if Nat.gcd m N = d then c m*χ (m/d) else 0 := by
    simp [gcdCharacterTransform,additiveGCDFibre,Finset.sum_filter]
  simp only [gcdCharacterContribution,dite_eq_right hqpos.ne']
  simp_rw [he]
  apply Summable.mul_left
  apply summable_sum
  intro χ _
  exact (gcd_character_terms_summable N d c hc χ).mul_left _

/-- Infinite gcd/character decomposition for arbitrary absolutely summable
coefficients. In applications the coefficient at zero is set to zero. -/
theorem additive_series_character_decomposition (N : ℕ) [NeZero N]
    (c : ℕ → ℂ) (hc : Summable c) :
    (∑' m : ℕ, c m*naturalAdditivePhase N m) =
      ∑ d ∈ N.divisors, gcdCharacterSeriesContribution N d c := by
  have he (m : ℕ) : c m*naturalAdditivePhase N m =
      ∑ d ∈ N.divisors, gcdCharacterContribution N d {m} c := by
    simpa using additive_sum_character_decomposition N {m} c
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun d hd => gcdCharacterContribution_summable N c hc hd)]
  apply Finset.sum_congr rfl
  intro d hd
  exact gcdCharacterContribution_tsum N c hc hd

def additiveDirichletSeriesBlock (N d : ℕ) (c : ℕ → ℂ) : ℂ :=
  if hq : N/d = 0 then 0 else
    letI : NeZero (N/d) := ⟨hq⟩
    ((N/d).totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ (N/d),
      gaussSum χ⁻¹ stdAddChar * χ (-1) * (∑' n : ℕ, c (d*n)*χ n)

/-- The additive series written entirely in terms of the genuine
reindexed character series. This is the absolute-convergence form of
the arithmetic identity (5.2). -/
theorem additive_series_character_decomposition_reindexed (N : ℕ) [NeZero N]
    (c : ℕ → ℂ) (hc : Summable c) :
    (∑' m : ℕ, c m*naturalAdditivePhase N m) =
      ∑ d ∈ N.divisors, additiveDirichletSeriesBlock N d c := by
  rw [additive_series_character_decomposition N c hc]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hqpos : 0 < N/d := Nat.div_pos
    (Nat.le_of_dvd hNpos (Nat.mem_divisors.mp hd).1) hdpos
  have : NeZero (N/d) := ⟨hqpos.ne'⟩
  simp only [gcdCharacterSeriesContribution,additiveDirichletSeriesBlock,dite_eq_right hqpos.ne']
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  rw [gcd_character_series_reindexed N c hd χ]

end
end Sechstmoment.Source
