import SixthMoment.Denominator.Gram.Algebra
import SixthMoment.Denominator.Gram.Analytic

namespace SixthMoment
open Complex Real MeasureTheory Set Polynomial Filter
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option maxHeartbeats 0

def d06ProjectedPolynomialGramMoment (τ σ : TestType) (T : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℝ :=
  ∫ t : ℝ, Φ (t / T) *
    (projectedZetaTest τ T t p (ρ 0) (ρ 1) *
      star (projectedZetaTest σ T t q (ρ 2) (ρ 3))).re

def d06WeightedComplexMoment (T : ℝ) (Φ : ℝ → ℝ) (F : ℝ → ℂ) : ℂ :=
  ∫ t : ℝ, (Φ (t / T) : ℂ) * F t

theorem d06_weighted_complex_integrable {T : ℝ} (hT : 0 < T)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (F : ℝ → ℂ) (hF : Continuous F) :
    Integrable (fun t => (Φ (t / T) : ℂ) * F t) := by
  have hc : Continuous (fun t => (Φ (t / T) : ℂ) * F t) := by
    exact ((Complex.continuous_ofReal.comp (hΦ.1.continuous.comp (by fun_prop))).mul hF)
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc T (2*T)))
  intro t ht
  have hz : Φ (t / T) ≠ 0 := by
    intro hz
    simp [Function.mem_support, hz] at ht
  have hx := hΦ.2 (subset_tsupport Φ hz)
  exact ⟨by simpa only [one_mul] using (le_div_iff₀ hT).mp hx.1,
    (div_le_iff₀ hT).mp hx.2⟩

theorem d06_weighted_realPart {T : ℝ} (hT : 0 < T)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t : ℝ, Φ (t/T) * (F t).re) = (d06WeightedComplexMoment T Φ F).re := by
  have hi := d06_weighted_complex_integrable hT Φ hΦ F hF
  have hir := integral_re hi
  change (∫ t : ℝ, ((Φ (t/T) : ℂ) * F t).re) =
    (∫ t : ℝ, (Φ (t/T) : ℂ) * F t).re at hir
  simpa only [d06WeightedComplexMoment, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using hir

theorem d06_weighted_half_realPart_three {T : ℝ} (hT : 0 < T)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (F G H : ℝ → ℂ)
    (hF : Continuous F) (hG : Continuous G) (hH : Continuous H) :
    (∫ t : ℝ, Φ (t/T) * ((1/2 : ℂ) * (((F t + G t + H t).re : ℝ) : ℂ)).re) =
      ((d06WeightedComplexMoment T Φ F).re + (d06WeightedComplexMoment T Φ G).re +
        (d06WeightedComplexMoment T Φ H).re) / 2 := by
  have hIf := d06_weighted_complex_integrable hT Φ hΦ F hF
  have hIg := d06_weighted_complex_integrable hT Φ hΦ G hG
  have hIh := d06_weighted_complex_integrable hT Φ hΦ H hH
  have he : d06WeightedComplexMoment T Φ (fun t => F t + G t + H t) =
      d06WeightedComplexMoment T Φ F + d06WeightedComplexMoment T Φ G +
        d06WeightedComplexMoment T Φ H := by
    unfold d06WeightedComplexMoment
    simp_rw [mul_add]
    have hab := integral_add hIf hIg
    have habc := integral_add (hIf.add hIg) hIh
    simp only [Pi.add_apply] at hab habc
    rw [habc, hab]
  calc
    _ = (1/2 : ℝ) * (∫ t : ℝ, Φ (t/T) * (F t + G t + H t).re) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      norm_num [Complex.mul_re]
      ring
    _ = _ := by
      rw [d06_weighted_realPart hT Φ hΦ (fun t => F t+G t+H t) ((hF.add hG).add hH), he,
        Complex.add_re, Complex.add_re]
      ring

theorem d06_profile_zero_above {a : ℝ} {f : ℝ → ℝ} (hs : tsupport f ⊆ Icc 0 a) :
    ∀ x, a < x → f x = 0 := by
  intro x hx
  by_contra hn
  exact (not_le_of_gt hx) (hs (subset_tsupport f hn)).2

end
end SixthMoment
