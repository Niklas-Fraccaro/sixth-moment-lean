import Sechstmoment.Analysis.Harmonic.PolynomialProfile

/-! Exact support identities for the literal finite profile sums. -/

namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set Polynomial
open scoped BigOperators Topology
noncomputable section

theorem rawStep_zero_of_nonpos {L t : ℝ} (hL : 0 < L) (ht : t ≤ 0)
    (ν : ℂ) (f : ℝ → ℂ) : rawStep L ν f t = 0 := by
  unfold rawStep
  apply Finset.sum_eq_zero
  intro n hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hx : 0 ≤ Real.log n/L := div_nonneg (Real.log_nonneg hn1) hL.le
  exact ite_eq_right (by linarith)

theorem rawIter_zero_of_nonpos {L t : ℝ} (hL : 0 < L) (ht : t ≤ 0)
    (ν : ℂ) (νs : List ℂ) (f : ℝ → ℂ) : rawIter L (ν::νs) f t = 0 :=
  rawStep_zero_of_nonpos hL ht ν _

theorem rawIter_max_zero {L : ℝ} (hL : 0 < L) (ν : ℂ) (νs : List ℂ)
    (f : ℝ → ℂ) (t : ℝ) : rawIter L (ν::νs) f (max 0 t) = rawIter L (ν::νs) f t := by
  rcases le_total 0 t with ht | ht
  · rw [max_eq_right ht]
  · rw [max_eq_left ht,rawIter_zero_of_nonpos hL le_rfl,rawIter_zero_of_nonpos hL ht]

theorem polynomialTripleSum_eq_unclipped {L : ℝ} (hL : 0 < L)
    (η : ℝ) (P : ℝ[X]) (ν₁ ν₂ ν₃ : ℂ) (d : ℕ) :
    polynomialTripleSum η L P ν₁ ν₂ ν₃ d =
      rawIter L [ν₁,ν₂,ν₃] (reversedPolynomial η P) (η-Real.log d/L) :=
  rawIter_max_zero hL ν₁ [ν₂,ν₃] _ _

theorem rawStep_enlarge {L t a : ℝ} (hL : 0 < L) (hta : t ≤ a)
    (ν : ℂ) (f : ℝ → ℂ) :
    rawStep L ν f t = ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*a)⌋₊,
      if Real.log n/L < t then
        (n:ℂ)^(-(1+ν/(L:ℂ)))*f (t-Real.log n/L) else 0 := by
  unfold rawStep
  apply Finset.sum_subset
  · intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      (Finset.mem_Icc.mp hn).2.trans
        (Nat.floor_mono (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hta hL.le)))⟩
  · intro n hn hnot
    have hN : ⌊Real.exp (L*t)⌋₊ < n := by
      have := (Finset.mem_Icc.mp hn).1
      simp only [Finset.mem_Icc,not_and] at hnot
      exact Nat.lt_of_not_ge (hnot this)
    have hlog : L*t < Real.log n := by
      simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos (L*t)) (Nat.lt_of_floor_lt hN)
    have hx : ¬ Real.log n/L < t := by
      have := (lt_div_iff₀ hL).mpr (by nlinarith : t*L < Real.log n)
      linarith
    exact ite_eq_right hx

def fixedIter (L a : ℝ) : List ℂ → (ℝ → ℂ) → ℝ → ℂ
  | [], f, t => f t
  | ν::νs, f, t => ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*a)⌋₊,
      if Real.log n/L < t then (n:ℂ)^(-(1+ν/(L:ℂ)))*
        fixedIter L a νs f (t-Real.log n/L) else 0

theorem rawIter_eq_fixed {L a t : ℝ} (hL : 0 < L) (hta : t ≤ a)
    (νs : List ℂ) (f : ℝ → ℂ) : rawIter L νs f t = fixedIter L a νs f t := by
  induction νs generalizing t with
  | nil => rfl
  | cons ν νs ih =>
    change rawStep L ν (rawIter L νs f) t = _
    rw [rawStep_enlarge hL hta]
    apply Finset.sum_congr rfl
    intro n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hx : 0 ≤ Real.log n/L := div_nonneg (Real.log_nonneg hn1) hL.le
    split_ifs
    · rw [ih (t := t-Real.log n/L) (by linarith)]
    · rfl

theorem polynomialTripleSum_eq_fixed {L : ℝ} (hL : 0 < L)
    (η : ℝ) (P : ℝ[X]) (ν₁ ν₂ ν₃ : ℂ) {d : ℕ} (hd : 1 ≤ d) :
    polynomialTripleSum η L P ν₁ ν₂ ν₃ d =
      fixedIter L η [ν₁,ν₂,ν₃] (reversedPolynomial η P) (η-Real.log d/L) := by
  rw [polynomialTripleSum_eq_unclipped hL]
  have hlog : 0 ≤ Real.log d/L := div_nonneg (Real.log_nonneg (by exact_mod_cast hd)) hL.le
  exact rawIter_eq_fixed hL (by linarith) _ _

end
end Sechstmoment.Source.NoDPHarmonic
