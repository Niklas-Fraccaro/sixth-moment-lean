import Sechstmoment.Analysis.Harmonic.Support

/-! The iterated finite sum is the literal three-variable logarithmic simplex,
with one strict support condition and ordinary complex powers. -/

namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set Polynomial
open scoped BigOperators Topology
noncomputable section

private theorem prefix_sum_eq (S : Finset ℕ) (x : ℕ → ℝ)
    (hx : ∀ n ∈ S, 0 ≤ x n) (p q r : ℕ → ℂ) (f : ℝ → ℂ) (t : ℝ) :
    (∑ n ∈ S, if x n < t then p n*
      (∑ m ∈ S, if x m < t-x n then q m*
        (∑ k ∈ S, if x k < t-x n-x m then r k*f (t-x n-x m-x k) else 0) else 0) else 0) =
    ∑ n ∈ S, ∑ m ∈ S, ∑ k ∈ S,
      if x n+x m+x k < t then p n*q m*r k*f (t-x n-x m-x k) else 0 := by
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h₁ : x n < t
  · rw [ite_eq_left h₁,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases h₂ : x m < t-x n
    · rw [ite_eq_left h₂,← mul_assoc,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h₃ : x k < t-x n-x m
      · rw [ite_eq_left h₃,ite_eq_left (by linarith : x n+x m+x k < t)]
        ring
      · rw [ite_eq_right h₃,ite_eq_right (by linarith : ¬ x n+x m+x k < t),mul_zero]
    · rw [ite_eq_right h₂,mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      exact ite_eq_right (by linarith [hx k hk])
  · rw [ite_eq_right h₁]
    symm
    apply Finset.sum_eq_zero
    intro m hm
    apply Finset.sum_eq_zero
    intro k hk
    exact ite_eq_right (by linarith [hx m hm,hx k hk])

def literalTripleSum (η L : ℝ) (P : ℝ[X]) (ν₁ ν₂ ν₃ : ℂ) (d : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
    ∑ m ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
      ∑ k ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
        if Real.log n/L+Real.log m/L+Real.log k/L < η-Real.log d/L then
          (n:ℂ)^(-(1+ν₁/(L:ℂ)))*(m:ℂ)^(-(1+ν₂/(L:ℂ)))*(k:ℂ)^(-(1+ν₃/(L:ℂ)))*
            ((P.eval ((η-Real.log d/L-Real.log n/L-Real.log m/L-Real.log k/L)/η):ℝ):ℂ)
        else 0

theorem polynomialTripleSum_eq_literal {L : ℝ} (hL : 0 < L)
    (η : ℝ) (P : ℝ[X]) (ν₁ ν₂ ν₃ : ℂ) {d : ℕ} (hd : 1 ≤ d) :
    polynomialTripleSum η L P ν₁ ν₂ ν₃ d = literalTripleSum η L P ν₁ ν₂ ν₃ d := by
  rw [polynomialTripleSum_eq_fixed hL η P ν₁ ν₂ ν₃ hd]
  simpa only [fixedIter,reversedPolynomial,literalTripleSum] using
    prefix_sum_eq (Finset.Icc 1 ⌊Real.exp (L*η)⌋₊) (fun n => Real.log n/L)
      (fun n hn => div_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hn).1)) hL.le)
      (fun n => (n:ℂ)^(-(1+ν₁/(L:ℂ)))) (fun n => (n:ℂ)^(-(1+ν₂/(L:ℂ))))
      (fun n => (n:ℂ)^(-(1+ν₃/(L:ℂ)))) (reversedPolynomial η P) (η-Real.log d/L)

theorem literal_polynomial_simplex_asymptotic {η R : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R)
    (P : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ ν₁ ν₂ ν₃ : ℂ,
      ‖ν₁‖ ≤ R → ‖ν₂‖ ≤ R → ‖ν₃‖ ≤ R → ∀ d : ℕ, 1 ≤ d →
      ‖literalTripleSum η L P ν₁ ν₂ ν₃ d -
          (L:ℂ)^3*polynomialSimplexIntegral η P ν₁ ν₂ ν₃‖ ≤ C*(1+Real.log d)*L^2 := by
  obtain ⟨C,hC,H⟩ := polynomial_simplex_asymptotic hη hR P
  refine ⟨C,hC,?_⟩
  intro L hL ν₁ ν₂ ν₃ hν₁ hν₂ hν₃ d hd
  rw [← polynomialTripleSum_eq_literal (by linarith : 0 < L) η P ν₁ ν₂ ν₃ hd]
  exact H L hL ν₁ ν₂ ν₃ hν₁ hν₂ hν₃ d hd

end
end Sechstmoment.Source.NoDPHarmonic
