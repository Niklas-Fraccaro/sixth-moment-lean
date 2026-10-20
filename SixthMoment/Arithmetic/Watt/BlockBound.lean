import SixthMoment.Arithmetic.Watt.BlockParameters


namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

def blockIntegrand (p : WattScales) (A : ℝ) (i j k : ℕ) (τ σ : ℤ)
    (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (y : ℝ) : ℂ :=
  complexWeightedSum (blockScales p A i j k) σ a bc
    (weightedBlock u₀ p.H i) (weightedBlock u₁ p.C j)
    (oscillatoryBlock (positiveFrequencyProfile (A/2)) A k ((τ : ℝ)*y)) (curveWeight γ y)

end
end Watt41

noncomputable section

theorem Watt41.completedBlock_bound (hWatt : Watt41) {ε : ℝ} (hε : 0 < ε)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (g : ℕ → ℕ → ℝ) (hg : ∀ i j, 0 ≤ g i j) :
    ∃ C F : ℝ, 0 ≤ C ∧ 1 ≤ F ∧
      ∀ (p : WattScales) (Δ E : ℝ) (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
        (γ : ℕ → ℕ → ℝ → ℝ → ℂ),
        (∀ n, 1 ≤ p.size n) → 0 < Δ → Δ ≤ 1 → 1 ≤ E →
        WattWeightData b g p Δ a bc u₀ u₁ γ →
        F*E ≤ p.X → p.H^2*p.C ≤ (p.R*p.S)^2 →
        Watt41.dualLength p E ≤ (p.R*p.S)^2 →
        ∀ (i j k : ℕ) (τ σ : ℤ),
          1 ≤ Watt41.blockScale p.H i → 1 ≤ Watt41.blockScale p.C j →
          1 ≤ Watt41.blockScale (Watt41.dualLength p E) k → (τ = -1 ∨ τ = 1) → (σ = -1 ∨ σ = 1) →
          ∀ y : ℝ, 0 < y → Watt41.dualLength p E*|y| ≤ 4*E →
            ‖Watt41.blockIntegrand p (Watt41.dualLength p E) i j k τ σ a bc u₀ u₁ γ y‖ ≤
              C*Watt41.majorant (Watt41.blockScales p (Watt41.dualLength p E) i j k) (Δ/E) ε := by
  obtain ⟨B,hB,hInner⟩ := Watt41.completedBlock_inner_data b hb
  obtain ⟨C,F,hC,hF,hbound⟩ := hWatt.complexWeightedCurve hε B g hB hg
  refine ⟨C,F,hC,hF,?_⟩
  intro p Δ E a bc u₀ u₁ γ hp hΔ hΔ₁ hE hw hlarge hfirst hsecond i j k τ σ hi hj hk hτ hσ y hy hyA
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hC' : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  have hEp : 0 < E := by linarith
  have hA := Watt41.dualLength_pos hS hP hV hEp
  have hτy : |(τ : ℝ)*y| = |y| := by
    rcases hτ with rfl | rfl <;> simp
  have hyA' : Watt41.dualLength p E*|(τ : ℝ)*y| ≤ 4*E := by rwa [hτy]
  have hdata := hInner g p Δ E (Watt41.dualLength p E) ((τ : ℝ)*y) a bc u₀ u₁ γ hw
    hH hC' hΔ hΔ₁ hE hA hyA' i j k
  exact hbound (Watt41.blockScales p (Watt41.dualLength p E) i j k) (Δ/E) σ a bc
    _ _ _ b p Δ a bc u₀ u₁ γ (Watt41.blockScales_sizes hp hi hj hk) (div_pos hΔ hEp) hσ hw
    hdata rfl hw.alpha_bound hw.beta_bound
    (Watt41.blockScales_size_conditions hH hC' hA hfirst hsecond i j k)
    (Watt41.blockScales_large_X hp hE hF hlarge i j k) y hy

end
end DivisorProof
