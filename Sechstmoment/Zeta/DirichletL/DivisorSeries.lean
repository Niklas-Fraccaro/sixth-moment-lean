import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.Convolution
import Sechstmoment.Zeta.DirichletL.SquareAFE


namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators LSeries.notation
noncomputable section

def dirichletDivisorCoefficients {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  (n.divisors.card : ℂ)*χ (n : ZMod N)

theorem dirichlet_square_convolution {N : ℕ} (χ : DirichletCharacter ℂ N) :
    LSeries.convolution (fun n : ℕ => χ n) (fun n : ℕ => χ n) =
      dirichletDivisorCoefficients χ := by
  funext n
  have hcard : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
  rw [LSeries.convolution_def]
  dsimp only
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal, χ (n : ZMod N) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
      calc
        _ = χ ((p.1*p.2 : ℕ) : ZMod N) := by rw [Nat.cast_mul, map_mul]
        _ = _ := by rw [hp']
    _ = dirichletDivisorCoefficients χ n := by
      simp [dirichletDivisorCoefficients, hcard, nsmul_eq_mul]

theorem dirichletL_square_hasSum {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (dirichletDivisorCoefficients χ) s ((χ.LFunction s)^2) := by
  have hf := (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs).LSeriesHasSum
  have h := hf.convolution hf
  rw [dirichlet_square_convolution] at h
  simpa only [DirichletCharacter.LFunction_eq_LSeries χ hs, pow_two] using h

theorem lSeriesTerm_vertical_continuous (f : ℕ → ℂ) (s : ℂ) (n : ℕ) :
    Continuous (fun v : ℝ => LSeries.term f (s+(v : ℂ)*I) n) := by
  by_cases hn : n = 0
  · simpa only [hn, LSeries.term_zero] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    simp only [LSeries.term_of_ne_zero hn]
    exact continuous_const.div
      ((by fun_prop : Continuous (fun v : ℝ => s+(v : ℂ)*I)).const_cpow (Or.inl hn'))
      (fun _ => by simp [hn'])

theorem lSeriesTerm_vertical_norm (f : ℕ → ℂ) (s : ℂ) (n : ℕ) (v : ℝ) :
    ‖LSeries.term f (s+(v : ℂ)*I) n‖ = ‖LSeries.term f s n‖ := by
  simp [LSeries.norm_term_eq]

theorem lSeries_vertical_integral_hasSum (f : ℕ → ℂ) (s : ℂ)
    (hf : LSeriesSummable f s) (K : ℝ → ℂ) (hK : Integrable K) :
    HasSum (fun n : ℕ => ∫ v : ℝ, K v*LSeries.term f (s+(v : ℂ)*I) n)
      (∫ v : ℝ, K v*LSeries f (s+(v : ℂ)*I)) := by
  apply hasSum_integral_of_dominated_convergence
    (fun n v => ‖K v‖*‖LSeries.term f s n‖)
  · intro n
    exact hK.aestronglyMeasurable.mul (lSeriesTerm_vertical_continuous f s n).aestronglyMeasurable
  · intro n
    exact Eventually.of_forall fun v => by rw [norm_mul, lSeriesTerm_vertical_norm]
  · exact Eventually.of_forall fun v => hf.norm.mul_left ‖K v‖
  · simpa only [tsum_mul_left] using hK.norm.mul_const (∑' n, ‖LSeries.term f s n‖)
  · exact Eventually.of_forall fun v =>
      (hf.of_re_le_re (by simp : s.re ≤ (s+(v : ℂ)*I).re)).hasSum.mul_left (K v)

end
end Sechstmoment.Source
