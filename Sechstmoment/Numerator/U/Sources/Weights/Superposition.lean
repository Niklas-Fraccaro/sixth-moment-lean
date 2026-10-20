import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Sechstmoment.Arithmetic.QuadraticDivisor.ComplexWeights


namespace Sechstmoment
open Source MeasureTheory Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

def phaseSourceMajorant (ε : ℝ) (q : QuadraticScales) : ℝ :=
  (q.mass*q.H^2)^ε*orientedQuadraticMajorant q+q.mass^ε*q.H^2

theorem phase_source_majorant_nonneg (ε : ℝ) (q : QuadraticScales)
    (hq : ∀ j, 0 ≤ q.size j) :
    0 ≤ phaseSourceMajorant ε q := by
  have hA := hq 0
  have hB := hq 1
  have hM₁ := hq 2
  have hM₂ := hq 3
  have hN₁ := hq 4
  have hN₂ := hq 5
  have hH := hq 6
  change 0 ≤ q.A at hA
  change 0 ≤ q.B at hB
  change 0 ≤ q.M₁ at hM₁
  change 0 ≤ q.M₂ at hM₂
  change 0 ≤ q.N₁ at hN₁
  change 0 ≤ q.N₂ at hN₂
  change 0 ≤ q.H at hH
  dsimp [phaseSourceMajorant, orientedQuadraticMajorant, QuadraticScales.mass,
    QuadraticScales.M, QuadraticScales.N]
  positivity

theorem phase_BBLRv1_integral_superposition
    (hinput : SeparatedQuadraticInput) {ε δ K : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
      (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Ω → Fin 5 → ℝ → ℂ) (c : Ω → ℂ),
      Integrable (fun ν => ‖c ν‖) μ →
      (∀ ν, QuadraticAdmissible (DivisorProof.inputExponent ε δ) δ K bounds q α β
        (fun i x => (W ν i x).re)) →
      (∀ ν i, RectangularComplexWeight (W ν i)) →
      (∀ ν j i x, ‖iteratedDeriv j (W ν i) x‖ ≤ bounds j*q.mass^(DivisorProof.inputExponent ε δ)) →
      ∀ positive : Bool,
      ‖∫ ν, c ν*rectangularComplexDiscrepancy positive q α β (W ν) ∂μ‖ ≤
        (C*phaseSourceMajorant ε q)*(∫ ν, ‖c ν‖ ∂μ) := by
  obtain ⟨C, hC, hsource⟩ := rectangular_BBLRv1_complex_weights
    hinput hε hδ hK bounds hbounds
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ q α β W c hc hadm hW hd positive
  have hb (ν : Ω) :
      ‖rectangularComplexDiscrepancy positive q α β (W ν)‖ ≤
        C*phaseSourceMajorant ε q :=
    hsource q α β (W ν) (hadm ν) (hW ν) (hd ν) positive
  calc
    _ ≤ ∫ ν, (C*phaseSourceMajorant ε q)*‖c ν‖ ∂μ :=
      norm_integral_le_of_norm_le (hc.const_mul _) (ae_of_all μ fun ν => by
        rw [norm_mul]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb ν) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

theorem phase_BBLRv1_summable_superposition
    (hinput : SeparatedQuadraticInput) {ε δ K : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type*)
      (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Ω → Fin 5 → ℝ → ℂ) (c : Ω → ℂ),
      Summable (fun ν => ‖c ν‖) →
      (∀ ν, QuadraticAdmissible (DivisorProof.inputExponent ε δ) δ K bounds q α β
        (fun i x => (W ν i x).re)) →
      (∀ ν i, RectangularComplexWeight (W ν i)) →
      (∀ ν j i x, ‖iteratedDeriv j (W ν i) x‖ ≤ bounds j*q.mass^(DivisorProof.inputExponent ε δ)) →
      ∀ positive : Bool,
      Summable (fun ν => c ν*rectangularComplexDiscrepancy positive q α β (W ν)) ∧
      ‖∑' ν, c ν*rectangularComplexDiscrepancy positive q α β (W ν)‖ ≤
        (C*phaseSourceMajorant ε q)*(∑' ν, ‖c ν‖) := by
  obtain ⟨C, hC, hsource⟩ := rectangular_BBLRv1_complex_weights
    hinput hε hδ hK bounds hbounds
  refine ⟨C, hC, ?_⟩
  intro Ω q α β W c hc hadm hW hd positive
  have hb (ν : Ω) :
      ‖c ν*rectangularComplexDiscrepancy positive q α β (W ν)‖ ≤
        (C*phaseSourceMajorant ε q)*‖c ν‖ := by
    rw [norm_mul]
    simpa only [mul_comm, phaseSourceMajorant] using mul_le_mul_of_nonneg_left
      (hsource q α β (W ν) (hadm ν) (hW ν) (hd ν) positive) (norm_nonneg (c ν))
  have hs := (hc.mul_left (C*phaseSourceMajorant ε q)).of_norm_bounded hb
  refine ⟨hs, ?_⟩
  calc
    _ ≤ ∑' ν, ‖c ν*rectangularComplexDiscrepancy positive q α β (W ν)‖ :=
      norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' ν, (C*phaseSourceMajorant ε q)*‖c ν‖ :=
      hs.norm.tsum_le_tsum hb (hc.mul_left _)
    _ = _ := tsum_mul_left

theorem phase_BBLRv1_integral_varying_coefficients
    (hinput : SeparatedQuadraticInput) {ε δ K : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
      (q : QuadraticScales) (α β : Ω → ℕ → ℂ)
      (W : Ω → Fin 5 → ℝ → ℂ) (c : Ω → ℂ),
      Integrable (fun ν => ‖c ν‖) μ →
      (∀ ν, QuadraticAdmissible (DivisorProof.inputExponent ε δ) δ K bounds q (α ν) (β ν)
        (fun i x => (W ν i x).re)) →
      (∀ ν i, RectangularComplexWeight (W ν i)) →
      (∀ ν j i x, ‖iteratedDeriv j (W ν i) x‖ ≤ bounds j*q.mass^(DivisorProof.inputExponent ε δ)) →
      ∀ positive : Bool,
      ‖∫ ν, c ν*rectangularComplexDiscrepancy positive q (α ν) (β ν) (W ν) ∂μ‖ ≤
        (C*phaseSourceMajorant ε q)*(∫ ν, ‖c ν‖ ∂μ) := by
  obtain ⟨C, hC, hsource⟩ := rectangular_BBLRv1_complex_weights
    hinput hε hδ hK bounds hbounds
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ q α β W c hc hadm hW hd positive
  calc
    _ ≤ ∫ ν, (C*phaseSourceMajorant ε q)*‖c ν‖ ∂μ :=
      norm_integral_le_of_norm_le (hc.const_mul _) (ae_of_all μ fun ν => by
        rw [norm_mul]
        simpa only [mul_comm, phaseSourceMajorant] using mul_le_mul_of_nonneg_left
          (hsource q (α ν) (β ν) (W ν) (hadm ν) (hW ν) (hd ν) positive) (norm_nonneg (c ν)))
    _ = _ := integral_const_mul _ _

theorem phase_BBLRv1_integral_admissible_components
    (hinput : SeparatedQuadraticInput) {ε δ K : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hbounds : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω)
      (q : QuadraticScales) (α β : Ω → ℕ → ℂ)
      (W : Ω → Fin 5 → ℝ → ℂ) (c : Ω → ℂ),
      Integrable (fun ν => ‖c ν‖) μ →
      (∀ ν component, QuadraticAdmissible (DivisorProof.inputExponent ε δ) δ K bounds q (α ν) (β ν)
        (rectangularRealComponent (W ν) component)) →
      (∀ ν i, RectangularComplexWeight (W ν i)) →
      ∀ positive : Bool,
      ‖∫ ν, c ν*rectangularComplexDiscrepancy positive q (α ν) (β ν) (W ν) ∂μ‖ ≤
        (C*phaseSourceMajorant ε q)*(∫ ν, ‖c ν‖ ∂μ) := by
  obtain ⟨C, hC, hsource⟩ := hinput ε hε δ hδ K hK bounds hbounds
  refine ⟨32*C, by positivity, ?_⟩
  intro Ω _ μ q α β W c hc hadm hW positive
  have hb (ν : Ω) :
      ‖rectangularComplexDiscrepancy positive q (α ν) (β ν) (W ν)‖ ≤
        (32*C)*phaseSourceMajorant ε q := by
    have hq : 0 < q.M₂ := by
      have hs := (hadm ν (fun _ => false)).1 3
      change 1 ≤ q.M₂ at hs
      linarith
    rw [rectangular_complex_discrepancy_expand positive q hq (α ν) (β ν) (W ν) (hW ν)]
    calc
      _ ≤ ∑ component : Fin 5 → Bool, ‖rectangularComponentPhase component*
          signedQuadraticDiscrepancy positive q (α ν) (β ν)
            (rectangularRealComponent (W ν) component)‖ := norm_sum_le _ _
      _ ≤ ∑ _component : Fin 5 → Bool, C*phaseSourceMajorant ε q := by
        apply Finset.sum_le_sum
        intro component _
        rw [norm_mul, rectangular_component_phase_norm, one_mul]
        exact hsource q (α ν) (β ν) _ (hadm ν component) positive
      _ = _ := by simp; ring
  calc
    _ ≤ ∫ ν, ((32*C)*phaseSourceMajorant ε q)*‖c ν‖ ∂μ :=
      norm_integral_le_of_norm_le (hc.const_mul _) (ae_of_all μ fun ν => by
        rw [norm_mul]
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb ν) (norm_nonneg (c ν)))
    _ = _ := integral_const_mul _ _

end
end Sechstmoment
