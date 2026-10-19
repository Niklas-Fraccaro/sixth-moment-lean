import Sechstmoment.Numerator.U.Separation.ActualAmplifierCoefficients
import Sechstmoment.Numerator.U.Separation.SeparatedBlock

/-! The expansion error of actual localized amplifier coefficients is
bounded by the literal finite cardinality, uniformly in shifts and weights. -/
namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phaseActualSourceBlock_coefficient_budget (T : ℝ) (q : QuadraticScales)
    (hA : 0<q.A) (hB : 0<q.B) (f g : ℝ → ℝ) {F Gc : ℝ}
    (hF : 0≤F) (hGc : 0≤Gc) (hf : ∀ x, ‖f x‖≤F) (hg : ∀ x, ‖g x‖≤Gc)
    (α : MomentShifts) (z : ℂ) (hs : ∀ i, (-(1/2+α i+z)).re≤0) :
    (∑ n∈quadraticIndexSet q,
      ‖phaseActualAmplifierCoefficient T f q.A (n 0)*phaseActualAmplifierCoefficient T g q.B (n 1)*
        phaseBaseSmoothFactor q α z n‖)≤(quadraticIndexSet q).card*(F*Gc) := by
  calc
    _ ≤ ∑ _n∈quadraticIndexSet q, F*Gc := by
      apply Finset.sum_le_sum
      intro n _
      rw [norm_mul,norm_mul]
      calc
        _ ≤ (F*Gc)*1 := mul_le_mul
          (mul_le_mul (phaseActualAmplifierCoefficient_norm_le T f hA hF hf _)
            (phaseActualAmplifierCoefficient_norm_le T g hB hGc hg _)
            (norm_nonneg _) hF)
          (phaseBaseSmoothFactor_norm_le_one q α z hs n) (norm_nonneg _) (mul_nonneg hF hGc)
        _ = _ := mul_one _
    _ = _ := by simp

theorem phaseActualSourceBlock_uniform_remainder {a b θ : ℝ} (hθ : 0≤θ)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) (M : ℝ) :
    ∃ F Gc L : ℝ, 0≤F ∧ 0≤Gc ∧ 0<L ∧ ∀ T : ℝ, Real.exp 1≤T →
      (⌈L*Real.log T⌉₊:ℝ)≤(L+1)*Real.log T ∧
      ∀ q : QuadraticScales, 0<q.A → 0<q.B → 0<q.H → 0<q.N₁ → 0<q.N₂ →
      2*q.H/(q.B*q.N₁*q.N₂)≤1/4 →
      T*(2*q.H/(q.B*q.N₁*q.N₂))≤θ*Real.log T →
      ∀ α : MomentShifts, (∀ i, (-(1/2+α i)).re≤0) →
      ∀ z : ℂ, 0≤z.re → ∀ t : ℝ, |t|≤2*T → ∀ positive : Bool,
      ‖phaseSignedSourceBlock positive q α z
          (phaseActualAmplifierCoefficient T f q.A) (phaseActualAmplifierCoefficient T g q.B) t-
        ∑ k∈Finset.range ⌈L*Real.log T⌉₊, phaseSeparationScalar q (rectangularGapSign positive) t k*
          rectangularComplexQuadraticSum positive q (phaseActualAmplifierCoefficient T f q.A)
            (phaseAdjustedBeta q (phaseActualAmplifierCoefficient T g q.B) k) (phaseFiveWeights α z k)‖≤
        ((quadraticIndexSet q).card*(F*Gc))*T^(-M) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨Gc,hGc,hgb⟩ := rectangular_supported_profile_bounded g hg
  obtain ⟨L,hL,hb⟩ := phase_signed_source_block_uniform_remainder hθ M
  refine ⟨F,Gc,L,hF,hGc,hL,?_⟩
  intro T hT
  have hTpos : 0<T := (Real.exp_pos 1).trans_le hT
  refine ⟨(hb T hT).1,?_⟩
  intro q hA hB hH hN₁ hN₂ hr4 hTr α hα z hz t ht positive
  have hs (i : Fin 4) : (-(1/2+α i+z)).re≤0 := by
    have he := hα i
    simp only [Complex.neg_re,Complex.add_re] at he ⊢
    linarith
  exact ((hb T hT).2 q hB hH hN₁ hN₂ hr4 hTr α z
    (phaseActualAmplifierCoefficient T f q.A) (phaseActualAmplifierCoefficient T g q.B)
    (phaseActualAmplifierCoefficient_support T g hB) t ht positive).trans
      (mul_le_mul_of_nonneg_right
        (phaseActualSourceBlock_coefficient_budget T q hA hB f g hF hGc hfb hgb α z hs) (by positivity))

end
end Sechstmoment
