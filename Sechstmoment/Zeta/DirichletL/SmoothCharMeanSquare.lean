import Sechstmoment.Zeta.DirichletL.SmoothDivisorSeriesBound

/-! The uniform fixed-modulus mean square of the canonical smoothed divisor
transform. This theorem is unconditional and includes the convergence of
the actual coefficients entering the square AFE.
-/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

def dirichletSmoothTransform {N : ℕ} (χ : DirichletCharacter ℂ N)
    (s : ℂ) (a : ℕ) : ℂ := ∑' n : ℕ, dirichletSmoothCoefficients N s a n*χ n

theorem dirichletDivisorTerm_eq_smoothCoefficient {N : ℕ}
    (χ : DirichletCharacter ℂ N) (s : ℂ) (a n : ℕ) :
    LSeries.term (dirichletDivisorCoefficients χ) s n *
      squareSmoothWeight s a (Real.pi*(n : ℝ)/(N : ℝ)) =
      dirichletSmoothCoefficients N s a n*χ n := by
  by_cases hn : n = 0
  · simp [hn,dirichletSmoothCoefficients_zero]
  · rw [LSeries.term_of_ne_zero hn,dirichletSmoothCoefficients,LSeries.term_of_ne_zero hn]
    unfold dirichletDivisorCoefficients
    ring

theorem dirichletL_square_eq_smooth_transforms {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (χ.LFunction s)^2 = dirichletSmoothTransform χ s (dirichletParity χ) +
      (dirichletSquareDualFactor χ s)^2*
        dirichletSmoothTransform χ⁻¹ (1-s) (dirichletParity χ) := by
  have h := dirichletL_square_eq_canonical_smooth_series χ hχ hprim hs0 hs1
  simp_rw [dirichletDivisorTerm_eq_smoothCoefficient] at h
  exact h

theorem dirichletSmoothTransform_mean_square {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, ∀ _ : NeZero N,
      ∀ s : ℂ, s.re ∈ Icc (1/4 : ℝ) (3/4) → ∀ a : ℕ, a ≤ 1 →
      ∀ δ : ℝ, δ ∈ Icc (0 : ℝ) 1 → 1/2+ε ≤ s.re+δ →
      (∑ χ : DirichletCharacter ℂ N, ‖dirichletSmoothTransform χ s a‖^2) ≤
        K*(N : ℝ)^(1+2*δ)*(1+|s.im|)^12 := by
  obtain ⟨C,hC,hbound⟩ := dirichletSmoothCoefficients_weighted_l2 hε
  refine ⟨(charSeriesWeightConstant+1)*C, by
    have h := charSeriesWeightConstant_nonneg
    positivity, ?_⟩
  intro N hN s hs a ha δ hδ hsd
  have : NeZero N := hN
  have hNp : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNp
  obtain ⟨hw,hwbound⟩ := hbound N hNp s hs a ha δ hδ hsd
  have hchar := charSeries_weighted_l2_bound N (dirichletSmoothCoefficients N s a)
    (dirichletSmoothCoefficients_summable N hNp s hs a ha) hw
  have hφ : (N.totient : ℝ) ≤ N := by exact_mod_cast Nat.totient_le N
  have hS : 0 ≤ charSeriesWeightConstant := charSeriesWeightConstant_nonneg
  calc
    _ ≤ (N.totient : ℝ)*charSeriesWeightConstant*
        (∑' n : ℕ, ((n/N : ℕ)+1 : ℝ)^2*‖dirichletSmoothCoefficients N s a n‖^2) := hchar
    _ ≤ (N : ℝ)*(charSeriesWeightConstant+1)*(C*(1+|s.im|)^12*(N : ℝ)^(2*δ)) := by
      gcongr
      linarith
    _ = _ := by rw [Real.rpow_add hNr,Real.rpow_one]; ring

end
end Sechstmoment.Source
