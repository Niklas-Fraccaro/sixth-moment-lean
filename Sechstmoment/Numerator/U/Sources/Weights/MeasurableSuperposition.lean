import Mathlib.MeasureTheory.Integral.Prod
import Sechstmoment.Numerator.U.Sources.Weights.Superposition

/-! Measurability and absolute convergence of the literal source discrepancy.
The unchanged BBLR input supplies its bound; convergence is a consequence. -/
namespace Sechstmoment
open Source MeasureTheory Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_source_quadratic_sum_measurable {Ω : Type*} [MeasurableSpace Ω]
    (positive : Bool) (q : QuadraticScales) (α β : Ω → ℕ → ℂ)
    (W : Ω → Fin 5 → ℝ → ℂ)
    (hα : ∀ n, Measurable (fun ν => α ν n))
    (hβ : ∀ n, Measurable (fun ν => β ν n))
    (hW : ∀ i x, Measurable (fun ν => W ν i x)) :
    Measurable (fun ν => rectangularComplexQuadraticSum positive q (α ν) (β ν) (W ν)) := by
  unfold rectangularComplexQuadraticSum
  apply Finset.measurable_sum
  intro n _
  by_cases hr : signedQuadraticRelation positive n
  · simp only [hr, ite_true]
    exact ((hα _).mul (hβ _)).mul (Finset.measurable_prod _ fun i _ => hW i _)
  · simp only [hr, ite_false]
    exact measurable_const

theorem phase_source_zero_mode_measurable {Ω : Type*} [MeasurableSpace Ω]
    (q : QuadraticScales) (α β : Ω → ℕ → ℂ) (W : Ω → Fin 5 → ℝ → ℂ)
    (hα : ∀ n, Measurable (fun ν => α ν n))
    (hβ : ∀ n, Measurable (fun ν => β ν n))
    (hWm : ∀ i x, Measurable (fun ν => W ν i x))
    (hWc : ∀ ν i, Continuous (W ν i)) :
    Measurable (fun ν => rectangularComplexZeroMode q (α ν) (β ν) (W ν)) := by
  unfold rectangularComplexZeroMode
  apply Finset.measurable_sum
  intro n _
  apply ((hα _).mul (hβ _)).mul
  have hj (i : Fin 5) : Measurable (fun p : Ω × ℝ =>
      W p.1 i (rectangularZeroArguments q n p.2 i)) := by
    have h := measurable_uncurry_of_continuous_of_measurable
      (u := fun x : ℝ => fun ν : Ω => W ν i (rectangularZeroArguments q n x i))
      (fun ν => (hWc ν i).comp (by fin_cases i <;> simp only [rectangularZeroArguments] <;> fun_prop))
      (fun x => hWm i _)
    exact h.comp measurable_swap
  exact (Finset.measurable_prod _ fun i _ => hj i).stronglyMeasurable.integral_prod_right'.measurable

theorem phase_source_discrepancy_measurable {Ω : Type*} [MeasurableSpace Ω]
    (positive : Bool) (q : QuadraticScales) (α β : Ω → ℕ → ℂ)
    (W : Ω → Fin 5 → ℝ → ℂ)
    (hα : ∀ n, Measurable (fun ν => α ν n))
    (hβ : ∀ n, Measurable (fun ν => β ν n))
    (hWm : ∀ i x, Measurable (fun ν => W ν i x))
    (hWc : ∀ ν i, Continuous (W ν i)) :
    Measurable (fun ν => rectangularComplexDiscrepancy positive q (α ν) (β ν) (W ν)) :=
  (phase_source_quadratic_sum_measurable positive q α β W hα hβ hWm).sub
    (phase_source_zero_mode_measurable q α β W hα hβ hWm hWc)

theorem phase_source_bounded_discrepancy_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (positive : Bool) (q : QuadraticScales) (α β : Ω → ℕ → ℂ)
    (W : Ω → Fin 5 → ℝ → ℂ) (c : Ω → ℂ) (hc : Integrable c μ)
    (hα : ∀ n, Measurable (fun ν => α ν n))
    (hβ : ∀ n, Measurable (fun ν => β ν n))
    (hWm : ∀ i x, Measurable (fun ν => W ν i x))
    (hWc : ∀ ν i, Continuous (W ν i))
    (L : ℝ) (hL : ∀ ν, ‖rectangularComplexDiscrepancy positive q (α ν) (β ν) (W ν)‖ ≤ L) :
    Integrable (fun ν => c ν * rectangularComplexDiscrepancy positive q (α ν) (β ν) (W ν)) μ := by
  apply (hc.norm.const_mul L).mono'
    (hc.aestronglyMeasurable.mul
      (phase_source_discrepancy_measurable positive q α β W hα hβ hWm hWc).aestronglyMeasurable)
  exact ae_of_all μ fun ν => by
    change ‖c ν * rectangularComplexDiscrepancy positive q (α ν) (β ν) (W ν)‖ ≤ L * ‖c ν‖
    rw [norm_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hL ν) (norm_nonneg (c ν))

theorem phase_BBLRv1_component_discrepancy_bound
    (hinput : SeparatedQuadraticInput) {ε δ K : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℂ),
      (∀ component, QuadraticAdmissible (DivisorProof.inputExponent ε δ) δ K bounds q α β
        (rectangularRealComponent W component)) →
      (∀ i, RectangularComplexWeight (W i)) → ∀ positive : Bool,
      ‖rectangularComplexDiscrepancy positive q α β W‖ ≤ C * phaseSourceMajorant ε q := by
  obtain ⟨C, hC, hsource⟩ := hinput ε hε δ hδ K hK bounds hbounds
  refine ⟨32*C, by positivity, ?_⟩
  intro q α β W hadm hW positive
  have hq : 0 < q.M₂ := by
    have hs := (hadm (fun _ => false)).1 3
    change 1 ≤ q.M₂ at hs
    linarith
  rw [rectangular_complex_discrepancy_expand positive q hq α β W hW]
  calc
    _ ≤ ∑ component : Fin 5 → Bool, ‖rectangularComponentPhase component *
      signedQuadraticDiscrepancy positive q α β (rectangularRealComponent W component)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _component : Fin 5 → Bool, C * phaseSourceMajorant ε q := by
      apply Finset.sum_le_sum
      intro component _
      rw [norm_mul, rectangular_component_phase_norm, one_mul]
      exact hsource q α β _ (hadm component) positive
    _ = _ := by simp; ring

theorem phase_BBLRv1_integrable_component_source
    (hinput : SeparatedQuadraticInput) {ε δ K : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
      (q : QuadraticScales) (α β : Ω → ℕ → ℂ)
      (W : Ω → Fin 5 → ℝ → ℂ) (c : Ω → ℂ),
      Integrable c μ →
      (∀ n, Measurable (fun ν => α ν n)) →
      (∀ n, Measurable (fun ν => β ν n)) →
      (∀ i x, Measurable (fun ν => W ν i x)) →
      (∀ ν component, QuadraticAdmissible (DivisorProof.inputExponent ε δ) δ K bounds q (α ν) (β ν)
        (rectangularRealComponent (W ν) component)) →
      (∀ ν i, RectangularComplexWeight (W ν i)) → ∀ positive : Bool,
      Integrable (fun ν => c ν * rectangularComplexDiscrepancy positive q
        (α ν) (β ν) (W ν)) μ ∧
      ‖∫ ν, c ν * rectangularComplexDiscrepancy positive q (α ν) (β ν) (W ν) ∂μ‖ ≤
        (C * phaseSourceMajorant ε q) * (∫ ν, ‖c ν‖ ∂μ) := by
  obtain ⟨C, hC, hpoint⟩ := phase_BBLRv1_component_discrepancy_bound
    hinput hε hδ hK bounds hbounds
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ q α β W c hc hα hβ hWm hadm hW positive
  have hb := fun ν => hpoint q (α ν) (β ν) (W ν) (hadm ν) (hW ν) positive
  refine ⟨phase_source_bounded_discrepancy_integrable μ positive q α β W c hc
    hα hβ hWm (fun ν i => (hW ν i).1.continuous) _ hb, ?_⟩
  calc
    _ ≤ ∫ ν, (C * phaseSourceMajorant ε q) * ‖c ν‖ ∂μ :=
      norm_integral_le_of_norm_le (hc.norm.const_mul _)
        (ae_of_all μ fun ν => by
          rw [norm_mul]
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb ν) (norm_nonneg (c ν)))
    _ = _ := integral_const_mul _ _

end
end Sechstmoment
