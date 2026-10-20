import Sechstmoment.Analysis.Harmonic.LiteralSimplex
import Sechstmoment.Analysis.Profiles.Classes
import Sechstmoment.Numerator.V.Profiles.GammaConvolution


namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set Polynomial NoDPGlobalRest
open scoped BigOperators Topology
noncomputable section

def sourceTripleSum (η L : ℝ) (P : ℝ[X]) (ν₁ ν₂ ν₃ : ℂ) (d : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
    ∑ m ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
      ∑ k ∈ Finset.Icc 1 ⌊Real.exp (L*η)⌋₊,
        (n:ℂ)^(-(1+ν₁/(L:ℂ)))*(m:ℂ)^(-(1+ν₂/(L:ℂ)))*(k:ℂ)^(-(1+ν₃/(L:ℂ)))*
          (zeroExtendedPolynomialProfile η P
            ((Real.log d+Real.log n+Real.log m+Real.log k)/L):ℂ)

theorem polynomialTripleSum_eq_source {η L : ℝ} (hη : 0 < η) (hL : 0 < L)
    (P : ℝ[X]) (ν₁ ν₂ ν₃ : ℂ) {d : ℕ} (hd : 1 ≤ d) :
    polynomialTripleSum η L P ν₁ ν₂ ν₃ d = sourceTripleSum η L P ν₁ ν₂ ν₃ d := by
  rw [polynomialTripleSum_eq_literal hL η P ν₁ ν₂ ν₃ hd]
  unfold literalTripleSum sourceTripleSum
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro k hk
  let x := (Real.log d+Real.log n+Real.log m+Real.log k)/L
  have hx : x = Real.log d/L+Real.log n/L+Real.log m/L+Real.log k/L := by dsimp [x]; ring
  have hlog (a : ℕ) (ha : 1 ≤ a) : 0 ≤ Real.log a/L :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast ha)) hL.le
  have hxd := hlog d hd
  have hxn := hlog n (Finset.mem_Icc.mp hn).1
  have hxm := hlog m (Finset.mem_Icc.mp hm).1
  have hxk := hlog k (Finset.mem_Icc.mp hk).1
  have hx0 : 0 ≤ x := by linarith
  have harg : (η-Real.log d/L-Real.log n/L-Real.log m/L-Real.log k/L)/η = 1-x/η := by
    rw [hx]
    field_simp [hη.ne']
    ring
  by_cases hcut : Real.log n/L+Real.log m/L+Real.log k/L < η-Real.log d/L
  · have hmem : x ∈ Ico 0 η := ⟨hx0,by linarith⟩
    rw [ite_eq_left hcut,harg]
    change _ = _*(zeroExtendedPolynomialProfile η P x:ℂ)
    rw [zeroExtendedPolynomialProfile,Set.indicator_of_mem hmem]
  · have hmem : x ∉ Ico 0 η := by intro h; linarith [h.2]
    rw [ite_eq_right hcut]
    change 0 = _*(zeroExtendedPolynomialProfile η P x:ℂ)
    rw [zeroExtendedPolynomialProfile,Set.indicator_of_notMem hmem,Complex.ofReal_zero,mul_zero]

theorem source_polynomial_simplex_asymptotic {η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (P : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L → ∀ ν₁ ν₂ ν₃ : ℂ,
      ‖ν₁‖ ≤ R → ‖ν₂‖ ≤ R → ‖ν₃‖ ≤ R → ∀ d : ℕ, 1 ≤ d →
      ‖sourceTripleSum η L P ν₁ ν₂ ν₃ d -
          (L:ℂ)^3*polynomialSimplexIntegral η P ν₁ ν₂ ν₃‖ ≤ C*(1+Real.log d)*L^2 := by
  obtain ⟨C,hC,H⟩ := polynomial_simplex_asymptotic hη.le hR P
  refine ⟨C,hC,?_⟩
  intro L hL ν₁ ν₂ ν₃ hν₁ hν₂ hν₃ d hd
  rw [← polynomialTripleSum_eq_source hη (by linarith : 0 < L) P ν₁ ν₂ ν₃ hd]
  exact H L hL ν₁ ν₂ ν₃ hν₁ hν₂ hν₃ d hd

def sourceGammaProfileSum (η L : ℝ) (i : Fin 4) (s : Fin 4 → ℂ)
    (ν μ : Fin 3 → ℂ) (P Q : ℝ[X]) : ℂ :=
  ∑' n : ℕ × ℕ, gammaAt i s n *
    (sourceTripleSum η L P (ν 0) (ν 1) (ν 2) n.1*
      sourceTripleSum η L Q (μ 0) (μ 1) (μ 2) n.2)

theorem gammaProfileSum_eq_source {η L : ℝ} (hη : 0 < η) (hL : 0 < L)
    (i : Fin 4) (s : Fin 4 → ℂ) (ν μ : Fin 3 → ℂ) (P Q : ℝ[X]) :
    gammaProfileSum η L i s ν μ (reversedPolynomial η P) (reversedPolynomial η Q) =
      sourceGammaProfileSum η L i s ν μ P Q := by
  unfold gammaProfileSum sourceGammaProfileSum
  apply tsum_congr
  rintro ⟨d,e⟩
  by_cases hd : d = 0
  · subst d
    simp only [gammaAt,gamma_zero_left,zero_mul]
  by_cases he : e = 0
  · subst e
    simp only [gammaAt,gamma_zero_right,zero_mul]
  change gammaAt i s (d,e)*(polynomialTripleSum η L P (ν 0) (ν 1) (ν 2) d*
    polynomialTripleSum η L Q (μ 0) (μ 1) (μ 2) e) = _
  rw [polynomialTripleSum_eq_source hη hL P _ _ _ (Nat.one_le_iff_ne_zero.mpr hd),
    polynomialTripleSum_eq_source hη hL Q _ _ _ (Nat.one_le_iff_ne_zero.mpr he)]

end
end Sechstmoment.Source.NoDPHarmonic
