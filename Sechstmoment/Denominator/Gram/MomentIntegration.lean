import Sechstmoment.Denominator.Gram.MomentRegularity
import Sechstmoment.Denominator.Gram.PhaseDefinitions
import Sechstmoment.Denominator.Gram.ReflectionMoments

/-! Exact weighted integration of the actual Gram identities. -/
namespace Sechstmoment
open Complex Real MeasureTheory Set Polynomial Filter
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option maxHeartbeats 0

def d06ReflectionProductIntegrand (τ σ : TestType) (k : ℤ)
    (T t : ℝ) (p q : ℝ[X]) (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  (criticalChi t)^k * d06PolynomialAmplitude false τ T t p (ρ 0) (ρ 1) *
    d06ReflectionAmplitude σ T t q (ρ 2) (ρ 3)

theorem d06_gram_integrands_continuous {T : ℝ} (hT : 1 < T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hs : ∀ i, tsupport (ρ i) ⊆ Icc 0 (a i)) (p q : ℝ[X]) :
    Continuous (fun t => d06BalancedPolynomialIntegrand T t p q ρ) ∧
      Continuous (fun t => d06UnbalancedPlusPolynomialIntegrand T t p q ρ) ∧
      Continuous (fun t => d06UnbalancedMinusPolynomialIntegrand T t p q ρ) ∧
      ∀ τ σ k, Continuous (fun t => d06ReflectionProductIntegrand τ σ k T t p q ρ) := by
  have hcp := d06_zetaCp_continuous T p
  have hcq : Continuous (fun t => zetaPolynomialDerivative T q (1-criticalLinePoint t)) := by
    simpa only [d04_zetaCp_conj] using (d06_zetaCp_continuous T q).star
  have hpos (i : Fin 4) : Continuous (fun t => profileDirichletSum T (ρ i) (criticalLinePoint t)) :=
    (profileDirichletSum_continuous hT (a i) (ρ i) (d06_profile_zero_above (hs i))).comp
      (by unfold criticalLinePoint; fun_prop)
  have hneg (i : Fin 4) : Continuous (fun t => profileDirichletSum T (ρ i) (1-criticalLinePoint t)) :=
    (profileDirichletSum_continuous hT (a i) (ρ i) (d06_profile_zero_above (hs i))).comp
      (by unfold criticalLinePoint; fun_prop)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hcp.mul hcq).mul (((hpos 0).mul (hpos 1)).mul (hneg 2) |>.mul (hneg 3))
  · exact ((criticalChi_continuous.mul hcp).mul hcq).mul
      (((hpos 0).mul (hneg 1)).mul (hneg 2) |>.mul (hneg 3))
  · exact ((d04_criticalChi_inv_continuous.mul hcp).mul hcq).mul
      (((hpos 0).mul (hpos 1)).mul (hpos 2) |>.mul (hneg 3))
  · intro τ σ k
    exact ((criticalChi_continuous.zpow₀ k (fun t => Or.inl (criticalChi_ne_zero t))).mul
      (d06PolynomialAmplitude_continuous false τ hT (a 0) (a 1) p (ρ 0) (ρ 1)
        (d06_profile_zero_above (hs 0)) (d06_profile_zero_above (hs 1)))).mul
      (d06ReflectionAmplitude_continuous σ hT (a 2) (a 3) q (ρ 2) (ρ 3)
        (d06_profile_zero_above (hs 2)) (d06_profile_zero_above (hs 3)))

theorem d06UUReflectionIntegrand_eq_product (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) :
    d06UUReflectionIntegrand T t p q ρ = d06ReflectionProductIntegrand .U .U 0 T t p q ρ := by
  simp [d06UUReflectionIntegrand, d06ReflectionProductIntegrand, d06PolynomialAmplitude,
    d06ReflectionAmplitude, d02BalancedAmplifier, d06UUReflectedProfiles]
  ring

theorem d06UVReflectionIntegrand_eq_product (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) :
    d06UVReflectionIntegrand T t p q ρ = d06ReflectionProductIntegrand .U .V (-1) T t p q ρ := by
  simp [d06UVReflectionIntegrand, d06ReflectionProductIntegrand, d06PolynomialAmplitude,
    d06ReflectionAmplitude, d04UnbalancedAmplifier, d06UVReflectedProfiles]
  ring

theorem d06ProjectedGram_VV_reflected (T t : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) :
    projectedZetaTest .V T t p (ρ 0) (ρ 1) * star (projectedZetaTest .V T t q (ρ 2) (ρ 3)) =
      (1/2 : ℂ) * (((d06BalancedPolynomialIntegrand T t p q ρ +
        (criticalChi t)⁻¹ * (criticalChi t)⁻¹ * zetaCp T t p *
          zetaPolynomialDerivative T (reflectedTestPolynomial q) (1-criticalLinePoint t) *
            d06AllPositiveAmplifier T t ρ + d06ReflectionProductIntegrand .V .V (-2) T t p q ρ).re : ℝ) : ℂ) := by
  rw [d06ProjectedGram_VV]
  congr 2
  congr 1
  have he := d06PolynomialReflectionError_identity T t q
  unfold d06VVExtremePolynomialIntegrand d06ReflectionProductIntegrand
    d06PolynomialAmplitude d06ReflectionAmplitude d06AllPositiveAmplifier
  simp only [Bool.false_eq_true, ite_false, Fin.prod_univ_four, zpow_neg, zpow_ofNat, inv_pow]
  linear_combination (criticalChi t)⁻¹ ^ 2 * zetaCp T t p *
    profileDirichletSum T (ρ 0) (criticalLinePoint t) *
    profileDirichletSum T (ρ 1) (criticalLinePoint t) *
    profileDirichletSum T (ρ 2) (criticalLinePoint t) *
    profileDirichletSum T (ρ 3) (criticalLinePoint t) * he

theorem d06ProjectedPolynomialGramMoment_swap (τ σ : TestType) (T : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) :
    d06ProjectedPolynomialGramMoment τ σ T p q ρ Φ =
      d06ProjectedPolynomialGramMoment σ τ T q p ![ρ 2, ρ 3, ρ 0, ρ 1] Φ := by
  unfold d06ProjectedPolynomialGramMoment
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  simp
  ring

end
end Sechstmoment
