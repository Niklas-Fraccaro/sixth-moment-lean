import Sechstmoment.Denominator.Gram.KernelDefinitions
import Sechstmoment.Denominator.Gram.MomentIntegration
import Sechstmoment.Denominator.Gram.PhaseClosure
import Sechstmoment.Denominator.Unbalanced.Asymptotic

namespace Sechstmoment
open Complex Real MeasureTheory Set Polynomial Filter
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option maxHeartbeats 0

theorem d06WeightedComplexMoment_balanced (T : ℝ) (Φ : ℝ → ℝ)
    (p q : ℝ[X]) (ρ : Fin 4 → ℝ → ℝ) :
    d06WeightedComplexMoment T Φ (fun t => d06BalancedPolynomialIntegrand T t p q ρ) =
      d02BalancedPolynomialMoment T p q ρ Φ := by
  unfold d06WeightedComplexMoment d06BalancedPolynomialIntegrand d02BalancedPolynomialMoment
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem d06WeightedComplexMoment_plus (T : ℝ) (Φ : ℝ → ℝ)
    (p q : ℝ[X]) (ρ : Fin 4 → ℝ → ℝ) :
    d06WeightedComplexMoment T Φ (fun t => d06UnbalancedPlusPolynomialIntegrand T t p q ρ) =
      d04UnbalancedPlusPolynomialMoment T p q ρ Φ := by
  unfold d06WeightedComplexMoment d06UnbalancedPlusPolynomialIntegrand d04UnbalancedPlusPolynomialMoment
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem d06WeightedComplexMoment_minus (T : ℝ) (Φ : ℝ → ℝ)
    (p q : ℝ[X]) (ρ : Fin 4 → ℝ → ℝ) :
    d06WeightedComplexMoment T Φ (fun t => d06UnbalancedMinusPolynomialIntegrand T t p q ρ) =
      d04UnbalancedPolynomialMoment T p q ρ Φ := by
  unfold d06WeightedComplexMoment d06UnbalancedMinusPolynomialIntegrand d04UnbalancedPolynomialMoment
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem d06_projected_gram_limit_of_three (τ σ : TestType) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (F G H : ℝ → ℝ → ℂ) (L M N : ℝ)
    (hidentity : ∀ T t, projectedZetaTest τ T t p (ρ 0) (ρ 1) *
      star (projectedZetaTest σ T t q (ρ 2) (ρ 3)) =
        (1/2 : ℂ) * (((F T t + G T t + H T t).re : ℝ) : ℂ))
    (hcont : ∀ᶠ T : ℝ in atTop, Continuous (F T) ∧ Continuous (G T) ∧ Continuous (H T))
    (hF : Tendsto (fun T => d06WeightedComplexMoment T Φ (F T)/(T*(Real.log T)^9 : ℂ))
      atTop (𝓝 (L : ℂ)))
    (hG : Tendsto (fun T => d06WeightedComplexMoment T Φ (G T)/(T*(Real.log T)^9 : ℂ))
      atTop (𝓝 (M : ℂ)))
    (hH : Tendsto (fun T => d06WeightedComplexMoment T Φ (H T)/(T*(Real.log T)^9 : ℂ))
      atTop (𝓝 (N : ℂ))) :
    Tendsto (fun T => d06ProjectedPolynomialGramMoment τ σ T p q ρ Φ/(T*(Real.log T)^9))
      atTop (𝓝 ((L+M+N)/2)) := by
  have hl := (((Complex.continuous_re.continuousAt.tendsto.comp hF).add
    (Complex.continuous_re.continuousAt.tendsto.comp hG)).add
    (Complex.continuous_re.continuousAt.tendsto.comp hH)).div_const 2
  simp only [Function.comp_def, Complex.ofReal_re] at hl
  apply hl.congr'
  filter_upwards [hcont, eventually_gt_atTop (0 : ℝ)] with T hc hT
  unfold d06ProjectedPolynomialGramMoment
  simp_rw [hidentity T]
  rw [d06_weighted_half_realPart_three hT Φ hΦ (F T) (G T) (H T) hc.1 hc.2.1 hc.2.2]
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.div_ofReal_re]
  ring

theorem d06_reflection_product_limit (τ σ : TestType) (k : ℤ)
    (a : Fin 4 → ℝ) (ha : ∀ i,0<a i)
    (hp1 : a 0+a 1<1/2) (hp2 : a 2+a 3<1/2)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x,0≤Φ x)
    (p q : ℝ[X]) (hp : p.natDegree≤4) (hq : q.natDegree≤4) :
    Tendsto (fun T => d06WeightedComplexMoment T Φ
      (fun t => d06ReflectionProductIntegrand τ σ k T t p q ρ)/(T*(Real.log T)^9 : ℂ))
      atTop (𝓝 0) := by
  apply (d06ReflectionProductMoment_normalized_tendsto τ σ k a ha hp1 hp2
    ρ hρ hρs Φ hΦ hΦpos p q hp hq).congr'
  filter_upwards [] with T
  congr 1
  unfold d06WeightedComplexMoment d06ReflectionProductIntegrand
  apply integral_congr_ae
  filter_upwards [] with t
  ring

theorem d06_balanced_permutation_limit (e : Fin 4 ≃ Fin 4)
    (a : Fin 4 → ℝ) (ha : ∀ i,0<a i) (hsum : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (p q : ℝ[X]) (hp : p.natDegree≤4) (hq : q.natDegree≤4) :
    Tendsto (fun T => d06WeightedComplexMoment T Φ
      (fun t => d06BalancedPolynomialIntegrand T t p q (fun i => ρ (e i)))/
        (T*(Real.log T)^9 : ℂ)) atTop
      (𝓝 ((arithmeticFactor*(∫ x : ℝ,Φ x)*d02BalancedProfileKernel
        (fun i => p.coeff i.val) (fun i => q.coeff i.val) (fun i => ρ (e i)) : ℝ) : ℂ)) := by
  have he : (∑ i,a (e i)) = ∑ i,a i := e.sum_comp a
  simpa only [d06WeightedComplexMoment_balanced] using
    d02BalancedDenominatorAsymptotic_closed (fun i => a (e i)) (fun i => ha (e i))
      (by rw [he]; exact hsum) (fun i => ρ (e i)) (fun i => hρ (e i))
      (fun i => hρs (e i)) Φ hΦ.1 hΦ.2 p q hp hq

theorem d06_minus_permutation_limit (e : Fin 4 ≃ Fin 4)
    (a : Fin 4 → ℝ) (ha : ∀ i,0<a i) (hsum : (∑ i,a i)<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (p q : ℝ[X]) (hp : p.natDegree≤4) (hq : q.natDegree≤4) :
    Tendsto (fun T => d06WeightedComplexMoment T Φ
      (fun t => d06UnbalancedMinusPolynomialIntegrand T t p q (fun i => ρ (e i)))/
        (T*(Real.log T)^9 : ℂ)) atTop
      (𝓝 ((arithmeticFactor*(∫ x : ℝ,Φ x)*d04UnbalancedProfileKernel
        (fun i => p.coeff i.val) (fun i => q.coeff i.val) (fun i => ρ (e i)) : ℝ) : ℂ)) := by
  have he : (∑ i,a (e i)) = ∑ i,a i := e.sum_comp a
  simpa only [d06WeightedComplexMoment_minus] using
    d04UnbalancedMinusAsymptotic_closed (fun i => a (e i)) (fun i => ha (e i))
      (by rw [he]; exact hsum) (fun i => ρ (e i)) (fun i => hρ (e i))
      (fun i => hρs (e i)) Φ hΦ.1 hΦ.2 p q hp hq

theorem d06ProjectedPolynomialGramMoment_UU_normalized_tendsto
    (a : Fin 4 → ℝ) (ha : ∀ i,0<a i)
    (hp1 : a 0+a 1<1/2) (hp2 : a 2+a 3<1/2)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x,0≤Φ x)
    (p q : ℝ[X]) (hp : p.natDegree≤4) (hq : q.natDegree≤4) :
    Tendsto (fun T => d06ProjectedPolynomialGramMoment .U .U T p q ρ Φ/(T*(Real.log T)^9))
      atTop (𝓝 (arithmeticFactor*(∫ x : ℝ,Φ x)*d06GramKernel .U .U p q ρ)) := by
  have hsum : (∑ i,a i)<1 := by rw [Fin.sum_univ_four]; linarith
  have hqr : (reflectedTestPolynomial q).natDegree≤4 :=
    (d06_reflectedTestPolynomial_natDegree_le q).trans hq
  have he1 : (fun i => ρ (d06GramPerm0312 i)) = d06UUConjugateProfiles ρ := by
    funext i; fin_cases i <;> rfl
  have he2 : (fun i => ρ (d06GramPerm0213 i)) = d06UUReflectedProfiles ρ := by
    funext i; fin_cases i <;> rfl
  have h1 := d06_balanced_permutation_limit d06GramPerm0312 a ha hsum ρ hρ hρs Φ hΦ p q hp hq
  have h2 := d06_balanced_permutation_limit d06GramPerm0213 a ha hsum ρ hρ hρs Φ hΦ
    p (reflectedTestPolynomial q) hp hqr
  rw [he1] at h1
  rw [he2] at h2
  have h3 := d06_reflection_product_limit .U .U 0 a ha hp1 hp2 ρ hρ hρs Φ hΦ hΦpos p q hp hq
  have hcont : ∀ᶠ T : ℝ in atTop,
      Continuous (fun t => d06BalancedPolynomialIntegrand T t p q (d06UUConjugateProfiles ρ)) ∧
      Continuous (fun t => d06BalancedPolynomialIntegrand T t p (reflectedTestPolynomial q)
        (d06UUReflectedProfiles ρ)) ∧
      Continuous (fun t => d06ReflectionProductIntegrand .U .U 0 T t p q ρ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hc1 := d06_gram_integrands_continuous hT (fun i => a (d06GramPerm0312 i))
      (fun i => ρ (d06GramPerm0312 i)) (fun i => hρs (d06GramPerm0312 i)) p q
    have hc2 := d06_gram_integrands_continuous hT (fun i => a (d06GramPerm0213 i))
      (fun i => ρ (d06GramPerm0213 i)) (fun i => hρs (d06GramPerm0213 i)) p (reflectedTestPolynomial q)
    rw [he1] at hc1
    rw [he2] at hc2
    exact ⟨hc1.1,hc2.1,(d06_gram_integrands_continuous hT a ρ hρs p q).2.2.2 _ _ _⟩
  have hl := d06_projected_gram_limit_of_three .U .U p q ρ Φ hΦ
    (fun T t => d06BalancedPolynomialIntegrand T t p q (d06UUConjugateProfiles ρ))
    (fun T t => d06BalancedPolynomialIntegrand T t p (reflectedTestPolynomial q)
      (d06UUReflectedProfiles ρ))
    (fun T t => d06ReflectionProductIntegrand .U .U 0 T t p q ρ) _ _ 0
    (fun T t => by rw [← d06UUReflectionIntegrand_eq_product]; exact d06ProjectedGram_UU T t p q ρ)
    hcont h1 h2 h3
  convert hl using 1
  congr 1
  simp only [d06GramKernel]
  ring

theorem d06ProjectedPolynomialGramMoment_UV_normalized_tendsto
    (a : Fin 4 → ℝ) (ha : ∀ i,0<a i)
    (hp1 : a 0+a 1<1/2) (hp2 : a 2+a 3<1/2)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x,0≤Φ x)
    (p q : ℝ[X]) (hp : p.natDegree≤4) (hq : q.natDegree≤4) :
    Tendsto (fun T => d06ProjectedPolynomialGramMoment .U .V T p q ρ Φ/(T*(Real.log T)^9))
      atTop (𝓝 (arithmeticFactor*(∫ x : ℝ,Φ x)*d06GramKernel .U .V p q ρ)) := by
  have hsum : (∑ i,a i)<1 := by rw [Fin.sum_univ_four]; linarith
  have hqr : (reflectedTestPolynomial q).natDegree≤4 :=
    (d06_reflectedTestPolynomial_natDegree_le q).trans hq
  have he : (fun i => ρ (d06GramPerm0231 i)) = d06UVReflectedProfiles ρ := by
    funext i; fin_cases i <;> rfl
  have h1 : Tendsto (fun T => d06WeightedComplexMoment T Φ
      (fun t => d06UnbalancedPlusPolynomialIntegrand T t p q ρ)/(T*(Real.log T)^9 : ℂ))
      atTop (𝓝 ((arithmeticFactor*(∫ x : ℝ,Φ x)*d04UnbalancedPlusProfileKernel
        (fun i => p.coeff i.val) (fun i => q.coeff i.val) ρ : ℝ) : ℂ)) := by
    simpa only [d06WeightedComplexMoment_plus] using
      d04UnbalancedPlusAsymptotic_closed a ha hsum ρ hρ hρs Φ hΦ.1 hΦ.2 p q hp hq
  have h2 := d06_minus_permutation_limit d06GramPerm0231 a ha hsum ρ hρ hρs Φ hΦ
    p (reflectedTestPolynomial q) hp hqr
  rw [he] at h2
  have h3 := d06_reflection_product_limit .U .V (-1) a ha hp1 hp2 ρ hρ hρs Φ hΦ hΦpos p q hp hq
  have hcont : ∀ᶠ T : ℝ in atTop,
      Continuous (fun t => d06UnbalancedPlusPolynomialIntegrand T t p q ρ) ∧
      Continuous (fun t => d06UnbalancedMinusPolynomialIntegrand T t p (reflectedTestPolynomial q)
        (d06UVReflectedProfiles ρ)) ∧
      Continuous (fun t => d06ReflectionProductIntegrand .U .V (-1) T t p q ρ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hc1 := d06_gram_integrands_continuous hT a ρ hρs p q
    have hc2 := d06_gram_integrands_continuous hT (fun i => a (d06GramPerm0231 i))
      (fun i => ρ (d06GramPerm0231 i)) (fun i => hρs (d06GramPerm0231 i)) p (reflectedTestPolynomial q)
    rw [he] at hc2
    exact ⟨hc1.2.1,hc2.2.2.1,hc1.2.2.2 _ _ _⟩
  have hl := d06_projected_gram_limit_of_three .U .V p q ρ Φ hΦ
    (fun T t => d06UnbalancedPlusPolynomialIntegrand T t p q ρ)
    (fun T t => d06UnbalancedMinusPolynomialIntegrand T t p (reflectedTestPolynomial q)
      (d06UVReflectedProfiles ρ))
    (fun T t => d06ReflectionProductIntegrand .U .V (-1) T t p q ρ) _ _ 0
    (fun T t => by rw [← d06UVReflectionIntegrand_eq_product]; exact d06ProjectedGram_UV T t p q ρ)
    hcont h1 h2 h3
  convert hl using 1
  congr 1
  simp only [d06GramKernel]
  ring

theorem d06ProjectedPolynomialGramMoment_VV_normalized_tendsto
    (a : Fin 4 → ℝ) (ha : ∀ i,0<a i)
    (hp1 : a 0+a 1<1/2) (hp2 : a 2+a 3<1/2)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x,0≤Φ x)
    (p q : ℝ[X]) (hp : p.natDegree≤4) (hq : q.natDegree≤4) :
    Tendsto (fun T => d06ProjectedPolynomialGramMoment .V .V T p q ρ Φ/(T*(Real.log T)^9))
      atTop (𝓝 (arithmeticFactor*(∫ x : ℝ,Φ x)*d06GramKernel .V .V p q ρ)) := by
  have hsum : (∑ i,a i)<1 := by rw [Fin.sum_univ_four]; linarith
  let G : ℝ → ℝ → ℂ := fun T t =>
    (criticalChi t)⁻¹ * (criticalChi t)⁻¹ * zetaCp T t p *
      zetaPolynomialDerivative T (reflectedTestPolynomial q) (1-criticalLinePoint t) *
        d06AllPositiveAmplifier T t ρ
  have h1 := d06_balanced_permutation_limit (Equiv.refl (Fin 4)) a ha hsum ρ hρ hρs Φ hΦ p q hp hq
  have he (T : ℝ) : d06WeightedComplexMoment T Φ (G T) =
      d06ExtremeMinusPolynomialMoment T p (reflectedTestPolynomial q) ρ Φ := by
    unfold d06WeightedComplexMoment d06ExtremeMinusPolynomialMoment
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [G]
    ring
  have h2 : Tendsto (fun T => d06WeightedComplexMoment T Φ (G T)/(T*(Real.log T)^9 : ℂ))
      atTop (𝓝 0) := by
    simpa only [he] using d06ExtremeMinusPolynomialMoment_normalized_tendsto
      a ha hsum ρ hρ hρs hΦ.1 hΦ.2 p (reflectedTestPolynomial q)
  have h3 := d06_reflection_product_limit .V .V (-2) a ha hp1 hp2 ρ hρ hρs Φ hΦ hΦpos p q hp hq
  have hcont : ∀ᶠ T : ℝ in atTop,
      Continuous (fun t => d06BalancedPolynomialIntegrand T t p q ρ) ∧
      Continuous (G T) ∧
      Continuous (fun t => d06ReflectionProductIntegrand .V .V (-2) T t p q ρ) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hc := d06_gram_integrands_continuous hT a ρ hρs p q
    have hqneg : Continuous (fun t => zetaPolynomialDerivative T (reflectedTestPolynomial q)
        (1-criticalLinePoint t)) := by
      simpa only [d04_zetaCp_conj] using (d06_zetaCp_continuous T (reflectedTestPolynomial q)).star
    refine ⟨hc.1,?_,hc.2.2.2 _ _ _⟩
    exact (((d04_criticalChi_inv_continuous.mul d04_criticalChi_inv_continuous).mul
      (d06_zetaCp_continuous T p)).mul hqneg).mul
        (d06AllPositiveAmplifier_continuous hT ρ a hρs)
  have hl := d06_projected_gram_limit_of_three .V .V p q ρ Φ hΦ
    (fun T t => d06BalancedPolynomialIntegrand T t p q ρ) G
    (fun T t => d06ReflectionProductIntegrand .V .V (-2) T t p q ρ) _ 0 0
    (fun T t => d06ProjectedGram_VV_reflected T t p q ρ) hcont h1 h2 h3
  convert hl using 1
  congr 1
  simp only [d06GramKernel, Equiv.refl_apply]
  ring

theorem d06ProjectedPolynomialGramMoment_normalized_tendsto
    (τ σ : TestType) (a : Fin 4 → ℝ) (ha : ∀ i,0<a i)
    (hp1 : a 0+a 1<1/2) (hp2 : a 2+a 3<1/2)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x,0≤Φ x)
    (p q : ℝ[X]) (hp : p.natDegree≤4) (hq : q.natDegree≤4) :
    Tendsto (fun T => d06ProjectedPolynomialGramMoment τ σ T p q ρ Φ/(T*(Real.log T)^9))
      atTop (𝓝 (arithmeticFactor*(∫ x : ℝ,Φ x)*d06GramKernel τ σ p q ρ)) := by
  cases τ with
  | U =>
      cases σ with
      | U => exact d06ProjectedPolynomialGramMoment_UU_normalized_tendsto a ha hp1 hp2 ρ hρ hρs Φ hΦ hΦpos p q hp hq
      | V => exact d06ProjectedPolynomialGramMoment_UV_normalized_tendsto a ha hp1 hp2 ρ hρ hρs Φ hΦ hΦpos p q hp hq
  | V =>
      cases σ with
      | V => exact d06ProjectedPolynomialGramMoment_VV_normalized_tendsto a ha hp1 hp2 ρ hρ hρs Φ hΦ hΦpos p q hp hq
      | U =>
          let b : Fin 4 → ℝ := ![a 2,a 3,a 0,a 1]
          have hb : ∀ i,0<b i := by
            intro i; fin_cases i <;> dsimp [b] <;> exact ha _
          have hbc : ∀ i, Continuous (d06GramSwapProfiles ρ i) := by
            intro i; fin_cases i <;> dsimp [d06GramSwapProfiles] <;> exact hρ _
          have hbs : ∀ i, tsupport (d06GramSwapProfiles ρ i)⊆Icc 0 (b i) := by
            intro i; fin_cases i <;> dsimp [d06GramSwapProfiles,b] <;> exact hρs _
          have hl := d06ProjectedPolynomialGramMoment_UV_normalized_tendsto b hb hp2 hp1
            (d06GramSwapProfiles ρ) hbc hbs Φ hΦ hΦpos q p hq hp
          simpa only [d06GramKernel, d06GramSwapProfiles,
            d06ProjectedPolynomialGramMoment_swap .V .U] using hl

end
end Sechstmoment
