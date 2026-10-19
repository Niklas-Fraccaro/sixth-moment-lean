import Sechstmoment.Zeta.DirichletL.SquareContour

/-! The Gaussian direct/dual identity for the actual, uncompleted L-function.
The two integrals are defined from the proved completed contour decomposition;
none of their analytic properties is assumed as an input.
-/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

def conductorGammaFactor {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ)^(s/2) * χ.gammaFactor s

theorem dirichletGammaFactor_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    χ.gammaFactor s ≠ 0 := by
  classical
  unfold DirichletCharacter.gammaFactor
  split_ifs
  · exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · apply Complex.Gammaℝ_ne_zero_of_re_pos
    simpa using (show 0 < s.re+1 by linarith)

theorem conductorGammaFactor_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    conductorGammaFactor χ s ≠ 0 := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  exact mul_ne_zero
    (by simp [hN])
    (dirichletGammaFactor_ne_zero χ hs)

theorem conductorCompletedL_eq_gamma_mul_L {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    conductorCompletedL χ s = conductorGammaFactor χ s * χ.LFunction s := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)]
  unfold conductorCompletedL conductorGammaFactor
  field_simp [dirichletGammaFactor_ne_zero χ hs]

def dirichletSquareLIntegral {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  dirichletSquareCompletedIntegral χ s / (conductorGammaFactor χ s)^2

def dirichletSquareDualFactor {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  χ.rootNumber * conductorGammaFactor χ⁻¹ (1-s) / conductorGammaFactor χ s

/-- Exact smoothed square functional equation, with its direct and dual
integrals, for an actual primitive nontrivial Dirichlet L-function. -/
theorem dirichletL_square_smooth_decomposition {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    (χ.LFunction s)^2 = dirichletSquareLIntegral χ s +
      (dirichletSquareDualFactor χ s)^2 * dirichletSquareLIntegral χ⁻¹ (1-s) := by
  have hG := conductorGammaFactor_ne_zero χ hs0
  have hG' := conductorGammaFactor_ne_zero χ⁻¹
    (show 0 < (1-s).re by simp only [sub_re, one_re]; linarith)
  have h := dirichletCompletedL_square_smooth_decomposition χ hχ hprim s
  rw [conductorCompletedL_eq_gamma_mul_L χ hs0] at h
  unfold dirichletSquareLIntegral dirichletSquareDualFactor
  apply (mul_left_cancel₀ (pow_ne_zero 2 hG))
  field_simp
  linear_combination h

end
end Sechstmoment.Source
