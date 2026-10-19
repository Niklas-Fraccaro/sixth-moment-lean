import Sechstmoment.Numerator.U.Separation.LogarithmicPhaseTruncation
import Sechstmoment.Numerator.U.Separation.SeparatedGapKernel

/-! A single cutoff, fixed before all block data, controls the literal
five-product expansion on the logarithmic near range. -/
namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem phase_five_product_finite_identity (q : QuadraticScales)
    (hB : 0<q.B) (hH : 0<q.H) (hN₁ : 0<q.N₁) (hN₂ : 0<q.N₂)
    (α : MomentShifts) (z : ℂ) (A β : ℕ → ℂ) (sign t : ℝ)
    (n : Fin 7 → ℕ) (hb : 0<n 1) (hn₁ : 0<n 4) (hn₂ : 0<n 5) (N : ℕ) :
    (∑ k∈Finset.range N, phaseSeparationScalar q sign t k*(A (n 0)*phaseAdjustedBeta q β k (n 1)*
      ∏ i : Fin 5, phaseFiveWeights α z k i (rectangularWeightArguments q n i)))=
      (A (n 0)*β (n 1)*phaseBaseSmoothFactor q α z n)*
        ∑ k∈Finset.range N, phaseBinomialCoefficient (-(t:ℂ)*I) k*
          ((sign*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5):ℝ):ℂ)^k := by
  simp_rw [phase_five_product_summand_identity q hB hH hN₁ hN₂ α z A β sign t n hb hn₁ hn₂]
  rw [Finset.mul_sum]

theorem phase_five_product_uniform_remainder {θ : ℝ} (hθ : 0≤θ) (M : ℝ) :
    ∃ L : ℝ, 0<L ∧ ∀ T : ℝ, Real.exp 1≤T →
      (⌈L*Real.log T⌉₊:ℝ)≤(L+1)*Real.log T ∧
      ∀ q : QuadraticScales, 0<q.B → 0<q.H → 0<q.N₁ → 0<q.N₂ →
      ∀ α : MomentShifts, ∀ z : ℂ, ∀ A β : ℕ → ℂ, ∀ sign t r : ℝ,
      |t|≤2*T → 0≤r → r≤1/4 → T*r≤θ*Real.log T →
      ∀ n : Fin 7 → ℕ, 0<n 1 → 0<n 4 → 0<n 5 →
      |sign*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5)|≤r →
      ‖(A (n 0)*β (n 1)*phaseBaseSmoothFactor q α z n)*
        (1+((sign*(n 6:ℝ)/((n 1:ℝ)*n 4*n 5):ℝ):ℂ))^(-(t:ℂ)*I)-
        ∑ k∈Finset.range ⌈L*Real.log T⌉₊, phaseSeparationScalar q sign t k*
          (A (n 0)*phaseAdjustedBeta q β k (n 1)*
            ∏ i : Fin 5, phaseFiveWeights α z k i (rectangularWeightArguments q n i))‖≤
        ‖A (n 0)*β (n 1)*phaseBaseSmoothFactor q α z n‖*T^(-M) := by
  obtain ⟨L,hL,hb⟩ := phaseBinomial_logarithmic_cutoff hθ M
  refine ⟨L,hL,?_⟩
  intro T hT
  refine ⟨(hb T hT).1,?_⟩
  intro q hB hH hN₁ hN₂ α z A β sign t r ht hr hr4 hTr n hnb hnn₁ hnn₂ hx
  rw [phase_five_product_finite_identity q hB hH hN₁ hN₂ α z A β sign t n hnb hnn₁ hnn₂,
    ← mul_sub,norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((hb T hT).2 t r ht hr hr4 hTr _
      (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hx)) (norm_nonneg _)

end
end Sechstmoment
