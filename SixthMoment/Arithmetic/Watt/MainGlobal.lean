import SixthMoment.Arithmetic.Watt.BlockSummation

namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 4000000

theorem Watt41.smoothedSum_bound_raw (hW : Watt41) {η : ℝ} (hη : 0 < η)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (g : ℕ → ℕ → ℝ) (hg : ∀ i j, 0 ≤ g i j) :
    ∃ C F : ℝ, 0 ≤ C ∧ 1 ≤ F ∧
      ∀ (p : WattScales) (Δ E : ℝ) (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
        (γ : ℕ → ℕ → ℝ → ℝ → ℂ), (∀ n, 1 ≤ p.size n) → 0 < Δ → Δ ≤ 1 → 1 ≤ E →
        WattWeightData b g p Δ a bc u₀ u₁ γ → F*E ≤ p.X →
        p.H^2*p.C ≤ (p.R*p.S)^2 → Watt41.dualLength p E ≤ (p.R*p.S)^2 →
        ∀ (positive : Bool) (τ : ℤ), (τ = -1 ∨ τ = 1) →
          ‖Watt41.smoothedSum p (Watt41.dualLength p E) positive τ a bc u₀ u₁ γ‖ ≤
            C*Watt41.core p Δ*E^6*(Watt41.totalSize p)^(2*η) := by
  obtain ⟨C,F,hC,hF,hblock⟩ := hW.completedFiniteBlock_bound hη b hb g hg
  refine ⟨2048*C,F,by positivity,hF,?_⟩
  intro p Δ E a bc u₀ u₁ γ hp hΔ hΔ₁ hE hw hlarge hfirst hsecond positive τ hτ
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hK : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  have hEp : 0 < E := by linarith
  have hA := Watt41.dualLength_pos hS hP hV hEp
  have hcore : 0 ≤ Watt41.core p Δ := (mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans (hp 0))
    (zero_le_one.trans (hp 1))) (zero_le_one.trans (hp 2))) (zero_le_one.trans (hp 4))).trans
    (Watt41.core_ge_HCRV hp hΔ hΔ₁)
  have hM : 0 < Watt41.totalSize p := lt_of_lt_of_le zero_lt_one (Watt41.totalSize_ge_one hp)
  by_cases hAlong : 1 ≤ Watt41.dualLength p E
  · obtain ⟨NH,hNH,hNH'⟩ := Watt41.exists_final_block (hp 0)
    obtain ⟨NK,hNK,hNK'⟩ := Watt41.exists_final_block (hp 1)
    obtain ⟨NA,hNA,hNA'⟩ := Watt41.exists_final_block hAlong
    rw [Watt41.smoothedSum_eq_blocks hw hH hK hA hNH' hNK' hNA']
    calc
      _ ≤ ∑ i ∈ range (NH+1), ∑ j ∈ range (NK+1), ∑ k ∈ range (NA+1),
          (C*Watt41.majorant (Watt41.blockScales p (Watt41.dualLength p E) i j k) (Δ/E) η)*
            (4*p.V/(p.S*p.P)-p.V/(2*p.S*p.P)) := by
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro i hi
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro j hj
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro k hk
        exact hblock p Δ E a bc u₀ u₁ γ hp hΔ hΔ₁ hE hw hlarge hfirst hsecond i j k positive τ
          (Watt41.blockScale_ge_final hH.le hNH hi) (Watt41.blockScale_ge_final hK.le hNK hj)
          (Watt41.blockScale_ge_final hA.le hNA hk) hτ
      _ = C*(∑ i ∈ range (NH+1), ∑ j ∈ range (NK+1), ∑ k ∈ range (NA+1),
          Watt41.majorant (Watt41.blockScales p (Watt41.dualLength p E) i j k) (Δ/E) η*
            (4*p.V/(p.S*p.P)-p.V/(2*p.S*p.P))) := by simp only [mul_sum,mul_assoc]
      _ ≤ C*(2048*Watt41.core p Δ*E^6*(Watt41.totalSize p)^(2*η)) :=
        mul_le_mul_of_nonneg_left (Watt41.sum_block_majorants_le hp hΔ hE hη.le hNH hNK hNA) hC
      _ = _ := by ring
  · have hempty := Watt41.positiveRange_eq_empty_of_lt_one (lt_of_not_ge hAlong)
    simp only [Watt41.smoothedSum,Watt41.tripleSum,hempty,sum_empty,mul_zero,sum_const_zero,norm_zero]
    positivity

namespace Watt41

theorem loss_absorbed {p : WattScales} (hp : ∀ n, 1 ≤ p.size n) {η : ℝ} (hη : 0 ≤ η) :
    (p.product^η)^6*(totalSize p)^(2*η) ≤ (totalSize p)^(20*η) := by
  have hT : 0 < p.product := lt_of_lt_of_le zero_lt_one (product_ge_one hp)
  have hM : 0 < totalSize p := lt_of_lt_of_le zero_lt_one (totalSize_ge_one hp)
  have he : (p.product^η)^6 ≤ (totalSize p)^(6*η) := by
    rw [← Real.rpow_mul_natCast hT.le]
    have hr := Real.rpow_le_rpow hT.le (product_le_totalSize hp) (by positivity : 0 ≤ η*6)
    simpa only [Nat.cast_ofNat,mul_comm] using hr
  calc
    _ ≤ (totalSize p)^(6*η)*(totalSize p)^(2*η) := mul_le_mul_of_nonneg_right he (by positivity)
    _ = (totalSize p)^(8*η) := by rw [← Real.rpow_add hM]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (totalSize_ge_one hp) (by linarith)

end Watt41

theorem Watt41.smoothedSum_bound (hW : Watt41) {η : ℝ} (hη : 0 < η)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (g : ℕ → ℕ → ℝ) (hg : ∀ i j, 0 ≤ g i j) :
    ∃ C F : ℝ, 0 ≤ C ∧ 1 ≤ F ∧
      ∀ (p : WattScales) (Δ : ℝ) (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
        (γ : ℕ → ℕ → ℝ → ℝ → ℂ), (∀ n, 1 ≤ p.size n) → 0 < Δ → Δ ≤ 1 →
        WattWeightData b g p Δ a bc u₀ u₁ γ → F*p.product^η ≤ p.X →
        p.H^2*p.C ≤ (p.R*p.S)^2 → Watt41.dualLength p (p.product^η) ≤ (p.R*p.S)^2 →
        ∀ (positive : Bool) (τ : ℤ), (τ = -1 ∨ τ = 1) →
          ‖Watt41.smoothedSum p (Watt41.dualLength p (p.product^η)) positive τ a bc u₀ u₁ γ‖ ≤
            C*wattMajorant p Δ η := by
  obtain ⟨C,F,hC,hF,hbound⟩ := hW.smoothedSum_bound_raw hη b hb g hg
  refine ⟨C,F,hC,hF,?_⟩
  intro p Δ a bc u₀ u₁ γ hp hΔ hΔ₁ hw hlarge hfirst hsecond positive τ hτ
  have hE : 1 ≤ p.product^η := Real.one_le_rpow (Watt41.product_ge_one hp) hη.le
  apply (hbound p Δ (p.product^η) a bc u₀ u₁ γ hp hΔ hΔ₁ hE hw hlarge hfirst hsecond positive τ hτ).trans
  rw [Watt41.wattMajorant_eq_core]
  have hcore : 0 ≤ Watt41.core p Δ := (mul_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans (hp 0))
    (zero_le_one.trans (hp 1))) (zero_le_one.trans (hp 2))) (zero_le_one.trans (hp 4))).trans
    (Watt41.core_ge_HCRV hp hΔ hΔ₁)
  calc
    _ = (C*Watt41.core p Δ)*((p.product^η)^6*(Watt41.totalSize p)^(2*η)) := by ring
    _ ≤ (C*Watt41.core p Δ)*(Watt41.totalSize p)^(20*η) :=
      mul_le_mul_of_nonneg_left (Watt41.loss_absorbed hp hη.le) (mul_nonneg hC hcore)
    _ = _ := by ring

end
end DivisorProof
