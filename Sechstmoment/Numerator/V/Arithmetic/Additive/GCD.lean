import Sechstmoment.Numerator.V.Arithmetic.Additive.Characters

/-!
Exact finite gcd grouping of the additive transform. The coefficients are
arbitrary: shifted divisor coefficients and smooth weights may therefore
be substituted literally. There is no asymptotic premise in these identities.
-/

namespace Sechstmoment.Source
open Complex Real ZMod Finset
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 800000

def naturalAdditivePhase (N m : ℕ) : ℂ :=
  Complex.exp (-(2*(Real.pi : ℂ)*I)*(m : ℂ)/(N : ℂ))

theorem naturalAdditivePhase_eq_std (N : ℕ) [NeZero N] (m : ℕ) :
    naturalAdditivePhase N m = stdAddChar (-(m : ZMod N)) := by
  calc
    _ = Complex.exp (2*(Real.pi : ℂ)*I*((-(m : ℤ)) : ℂ)/(N : ℂ)) := by
      simp only [naturalAdditivePhase,Int.cast_natCast]
      congr 1
      ring
    _ = stdAddChar ((-(m : ℤ)) : ZMod N) :=
      by simpa only [Int.cast_neg] using (ZMod.stdAddChar_coe (N := N) (-(m : ℤ))).symm
    _ = _ := by simp

theorem naturalAdditivePhase_divisor {N m d : ℕ} (hd : d ≠ 0)
    (hdN : d ∣ N) (hdm : d ∣ m) :
    naturalAdditivePhase N m = naturalAdditivePhase (N/d) (m/d) := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hN : (N : ℂ) = (N/d : ℕ)*(d : ℂ) := by
    exact_mod_cast (Nat.div_mul_cancel hdN).symm
  have hm : (m : ℂ) = (m/d : ℕ)*(d : ℂ) := by
    exact_mod_cast (Nat.div_mul_cancel hdm).symm
  unfold naturalAdditivePhase
  rw [hN,hm]
  congr 1
  rw [← mul_assoc,mul_div_mul_right _ _ hdC]

def additiveGCDFibre (N d : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.filter (fun m => Nat.gcd m N = d)

theorem additive_sum_grouped_by_gcd (N : ℕ) [NeZero N]
    (s : Finset ℕ) (c : ℕ → ℂ) :
    (∑ m ∈ s, c m*naturalAdditivePhase N m) =
      ∑ d ∈ N.divisors, ∑ m ∈ additiveGCDFibre N d s,
        c m*naturalAdditivePhase (N/d) (m/d) := by
  have hmaps (m : ℕ) (_hm : m ∈ s) : Nat.gcd m N ∈ N.divisors :=
    Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right m N,NeZero.ne N⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun m => c m*naturalAdditivePhase N m)]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro m hm
  have he : Nat.gcd m N = d := (Finset.mem_filter.mp hm).2
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  rw [naturalAdditivePhase_divisor hd0 (Nat.mem_divisors.mp hd).1
    (he ▸ Nat.gcd_dvd_left m N)]

theorem additive_gcd_quotient_coprime {N m d : ℕ} (hN : 0 < N)
    (h : Nat.gcd m N = d) : Nat.Coprime (m/d) (N/d) := by
  rw [← h]
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right m hN)

def gcdCharacterTransform (N d : ℕ) (s : Finset ℕ) (c : ℕ → ℂ)
    (χ : DirichletCharacter ℂ (N/d)) : ℂ :=
  ∑ m ∈ additiveGCDFibre N d s, c m*χ (m/d)

/-- The exact inner character expansion of a gcd fibre, with the sign
factor outside the transformed coefficients. -/
theorem additive_gcd_fibre_character_expansion (N : ℕ) [NeZero N]
    (s : Finset ℕ) (c : ℕ → ℂ) {d : ℕ} (_hd : d ∈ N.divisors)
    [NeZero (N/d)] :
    (∑ m ∈ additiveGCDFibre N d s, c m*naturalAdditivePhase (N/d) (m/d)) =
      ((N/d).totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ (N/d), gaussSum χ⁻¹ stdAddChar * χ (-1) *
          gcdCharacterTransform N d s c χ := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hneg (χ : DirichletCharacter ℂ (N/d)) (m : ℕ) :
      χ (-(m : ZMod (N/d))) = χ (-1)*χ m := by
    rw [show -(m : ZMod (N/d)) = (-1)*(m : ZMod (N/d)) by ring,map_mul]
  calc
    _ = ∑ m ∈ additiveGCDFibre N d s, c m *
        (((N/d).totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ (N/d),
          gaussSum χ⁻¹ stdAddChar * χ (-((m/d : ℕ) : ZMod (N/d)))) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [naturalAdditivePhase_eq_std,← additive_character_expansion (N/d) _]
      apply IsUnit.neg
      exact (ZMod.isUnit_iff_coprime _ _).mpr
        (additive_gcd_quotient_coprime hNpos (Finset.mem_filter.mp hm).2)
    _ = _ := by
      unfold gcdCharacterTransform
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro χ _
      apply Finset.sum_congr rfl
      intro m _
      rw [hneg]
      ring

def gcdCharacterContribution (N d : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) : ℂ :=
  if hq : N/d = 0 then 0 else
    letI : NeZero (N/d) := ⟨hq⟩
    ((N/d).totient : ℂ)⁻¹ *
      ∑ χ : DirichletCharacter ℂ (N/d), gaussSum χ⁻¹ stdAddChar * χ (-1) *
        gcdCharacterTransform N d s c χ

/-- Complete finite additive character decomposition, uniformly including
the divisor `d = N`, hence modulus one. -/
theorem additive_sum_character_decomposition (N : ℕ) [NeZero N]
    (s : Finset ℕ) (c : ℕ → ℂ) :
    (∑ m ∈ s, c m*naturalAdditivePhase N m) =
      ∑ d ∈ N.divisors, gcdCharacterContribution N d s c := by
  rw [additive_sum_grouped_by_gcd]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hqpos : 0 < N/d := Nat.div_pos
    (Nat.le_of_dvd hNpos (Nat.mem_divisors.mp hd).1) hdpos
  have : NeZero (N/d) := ⟨hqpos.ne'⟩
  simp only [gcdCharacterContribution,dite_eq_right hqpos.ne']
  exact additive_gcd_fibre_character_expansion N s c hd

/-- Reindexing a gcd fibre gives precisely the reduced coprime progression.
There is no loss of endpoint terms in the quotient `M / d`. -/
theorem gcdCharacterTransform_interval (N : ℕ) [NeZero N]
    (M : ℕ) (c : ℕ → ℂ) {d : ℕ} (hd : d ∈ N.divisors)
    (χ : DirichletCharacter ℂ (N/d)) :
    gcdCharacterTransform N d (Finset.Icc 1 M) c χ =
      ∑ n ∈ Finset.Icc 1 (M/d) with Nat.Coprime n (N/d), c (d*n)*χ n := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdN := (Nat.mem_divisors.mp hd).1
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  unfold gcdCharacterTransform additiveGCDFibre
  apply Finset.sum_bij (fun m _ => m/d)
  · intro m hm
    obtain ⟨hm,he⟩ := Finset.mem_filter.mp hm
    have hdm : d ∣ m := he ▸ Nat.gcd_dvd_left m N
    have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,
      additive_gcd_quotient_coprime hNpos he⟩
    · exact Nat.div_pos (Nat.le_of_dvd hmpos hdm) hdpos
    · exact Nat.div_le_div_right (Finset.mem_Icc.mp hm).2
  · intro m hm n hn he
    have hdm : d ∣ m := (Finset.mem_filter.mp hm).2 ▸ Nat.gcd_dvd_left m N
    have hdn : d ∣ n := (Finset.mem_filter.mp hn).2 ▸ Nat.gcd_dvd_left n N
    have h := congrArg (fun k : ℕ => k*d) he
    simpa only [Nat.div_mul_cancel hdm,Nat.div_mul_cancel hdn] using h
  · intro n hn
    obtain ⟨hn,hcop⟩ := Finset.mem_filter.mp hn
    have he : Nat.gcd (d*n) N = d := by
      rw [show N = d*(N/d) from (Nat.mul_div_cancel' hdN).symm,
        Nat.gcd_mul_left,hcop.gcd_eq_one,mul_one]
    refine ⟨d*n,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_,?_⟩,he⟩,?_⟩
    · exact Nat.mul_pos hdpos (Finset.mem_Icc.mp hn).1
    · simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hdpos).mp (Finset.mem_Icc.mp hn).2
    · exact Nat.mul_div_cancel_left n hdpos
  · intro m hm
    have hdm : d ∣ m := (Finset.mem_filter.mp hm).2 ▸ Nat.gcd_dvd_left m N
    rw [Nat.mul_div_cancel' hdm]

/-- A character kills the noncoprime terms, so the reduced transform has
the exact unrestricted Dirichlet-polynomial shape used in (5.2). -/
theorem gcdCharacterTransform_interval_unrestricted (N : ℕ) [NeZero N]
    (M : ℕ) (c : ℕ → ℂ) {d : ℕ} (hd : d ∈ N.divisors)
    (χ : DirichletCharacter ℂ (N/d)) :
    gcdCharacterTransform N d (Finset.Icc 1 M) c χ =
      ∑ n ∈ Finset.Icc 1 (M/d), c (d*n)*χ n := by
  rw [gcdCharacterTransform_interval N M c hd χ]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hmem hn
  have hcop : ¬ Nat.Coprime n (N/d) := by
    intro h
    exact hn (Finset.mem_filter.mpr ⟨hmem,h⟩)
  have hunit : ¬ IsUnit (n : ZMod (N/d)) := by
    simpa only [ZMod.isUnit_iff_coprime] using hcop
  rw [MulChar.map_nonunit _ hunit,mul_zero]

def additiveDirichletBlock (N d M : ℕ) (c : ℕ → ℂ) : ℂ :=
  if hq : N/d = 0 then 0 else
    letI : NeZero (N/d) := ⟨hq⟩
    ((N/d).totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ (N/d),
      gaussSum χ⁻¹ stdAddChar * χ (-1) *
        (∑ n ∈ Finset.Icc 1 (M/d), c (d*n)*χ n)

/-- Finite version of the additive Dirichlet-series identity (5.2), with
arbitrary complex coefficients and exact quotient cutoffs. -/
theorem additive_interval_character_decomposition (N : ℕ) [NeZero N]
    (M : ℕ) (c : ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M, c m*naturalAdditivePhase N m) =
      ∑ d ∈ N.divisors, additiveDirichletBlock N d M c := by
  rw [additive_sum_character_decomposition]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hqpos : 0 < N/d := Nat.div_pos
    (Nat.le_of_dvd hNpos (Nat.mem_divisors.mp hd).1) hdpos
  have : NeZero (N/d) := ⟨hqpos.ne'⟩
  simp only [gcdCharacterContribution,additiveDirichletBlock,dite_eq_right hqpos.ne']
  congr 1
  apply Finset.sum_congr rfl
  intro χ _
  rw [gcdCharacterTransform_interval_unrestricted N M c hd χ]

end
end Sechstmoment.Source
