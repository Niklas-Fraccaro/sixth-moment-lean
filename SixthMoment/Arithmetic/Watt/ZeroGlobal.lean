import SixthMoment.Arithmetic.Watt.Aggregate

namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 4000000

theorem completedTerm_zero_of_p_outside {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (positive : Bool) (h k r s t : ℕ) (l : ℤ) (ht : (t : ℝ) ∉ Icc (p.P/2) p.P) :
    completedTerm p γ positive h k r s t l = 0 := by
  have heq : (fun v : ℝ => γ r s v t) = 0 := by
    funext v
    by_contra hn
    have hn' : (fun z : ℝ × ℝ => γ r s z.1 z.2) (v,t) ≠ 0 := hn
    exact ht (hw.gamma_support r s (subset_tsupport _ hn')).2
  have hz (v : ℝ) : γ r s v t = 0 := congrFun heq v
  simp only [completedTerm,fourierCoefficient,hz,zero_mul,integral_zero]

theorem zero_global_bound {η : ℝ} (hη : 0 < η)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (g : ℕ → ℕ → ℝ) (hg : ∀ i j, 0 ≤ g i j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : WattScales) (Δ : ℝ) (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
      (γ : ℕ → ℕ → ℝ → ℝ → ℂ), (∀ n, 1 ≤ p.size n) → 0 < Δ → Δ ≤ 1 →
      WattWeightData b g p Δ a bc u₀ u₁ γ → ∀ positive : Bool,
      ‖frequencySum p a bc u₀ u₁ γ positive 0‖ ≤ C*wattMajorant p Δ η := by
  obtain ⟨D,hD,hdiv⟩ := divisor_count_sq_subpower hη
  let C := 16*b 0^2*g 0 0*D
  have hg₀ := hg 0 0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p Δ a bc u₀ u₁ γ hp hΔ hΔ₁ hw positive
  have hH : 0 < p.H := lt_of_lt_of_le zero_lt_one (hp 0)
  have hK : 0 < p.C := lt_of_lt_of_le zero_lt_one (hp 1)
  have hR : 0 < p.R := lt_of_lt_of_le zero_lt_one (hp 2)
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  have hM : 0 < totalSize p := lt_of_lt_of_le zero_lt_one (totalSize_ge_one hp)
  have hSP : p.S*p.P ≤ totalSize p := by
    have hRV : 1 ≤ p.R*p.V := one_le_mul_of_one_le_of_one_le (hp 2) (hp 4)
    have hst : p.S*p.P ≤ p.product := by
      unfold WattScales.product
      nlinarith [mul_le_mul_of_nonneg_right hRV (mul_pos hS hP).le]
    exact hst.trans (product_le_totalSize hp)
  let B := b 0^2*(4*g 0 0)*(4*p.V/(p.S*p.P))*p.H*p.C*(D*(totalSize p)^η)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound := aggregate_fibre_bound hp a bc u₀ u₁
    (fun h k r s t => completedTerm p γ positive h k r s t 0)
    hw.alpha_bound hw.beta_bound hB
  have hnorm : ‖frequencySum p a bc u₀ u₁ γ positive 0‖ ≤ p.R*p.S*p.P*B := by
    rw [frequencySum_eq_aggregate]
    apply hbound
    intro rs hrs t ht
    have hs := mem_dyadicRange.mp (mem_product.mp (mem_filter.mp hrs).1).2
    change 1 ≤ rs.2 ∧ p.S/2 ≤ (rs.2 : ℝ) ∧ (rs.2 : ℝ) ≤ p.S at hs
    have htp := mem_positiveRange.mp (mem_filter.mp ht).1
    by_cases hti : (t : ℝ) ∈ Icc (p.P/2) p.P
    · have hsp : 0 < rs.2 := hs.1
      have hc : 0 < rs.2*t := Nat.mul_pos hsp htp.1
      have hcp : (0 : ℝ) < (rs.2*t : ℕ) := by exact_mod_cast hc
      have hr : rs.1.Coprime (rs.2*t) := (mem_filter.mp hrs).2.mul_right (mem_filter.mp ht).2.symm
      have hcard : ((rs.2*t).divisors.card : ℝ)^2 ≤ D*(totalSize p)^η := by
        apply (hdiv (rs.2*t) hc.ne').trans
        apply mul_le_mul_of_nonneg_left _ hD
        apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hη.le
        have hh : ((rs.2*t : ℕ) : ℝ) ≤ p.S*p.P := by
          simpa only [Nat.cast_mul] using mul_le_mul hs.2.2 htp.2 (Nat.cast_nonneg t) hS.le
        exact hh.trans hSP
      have hlower : p.S*p.P/4 ≤ ((rs.2*t : ℕ) : ℝ) := by
        have hh := mul_le_mul hs.2.1 hti.1 (by positivity : 0 ≤ p.P/2) (Nat.cast_nonneg rs.2)
        push_cast
        nlinarith
      have hfrac : p.V/(rs.2*t : ℕ) ≤ 4*p.V/(p.S*p.P) := by
        apply (div_le_div_iff₀ hcp (mul_pos hS hP)).mpr
        nlinarith [mul_le_mul_of_nonneg_left hlower hV.le]
      apply (zero_frequency_fibre_bound hw hb hg hH.le hK.le hV positive rs.1 hsp htp.1 hr).trans
      dsimp [B]
      gcongr
    · have hz (h k : ℕ) := completedTerm_zero_of_p_outside hw positive h k rs.1 rs.2 t 0 hti
      simpa only [hz,mul_zero,sum_const_zero,norm_zero] using hB
  have heq : p.R*p.S*p.P*B = C*(p.H*p.C*p.R*p.V)*(totalSize p)^η := by
    dsimp [B,C]
    field_simp [hS.ne',hP.ne']
    ring
  rw [heq] at hnorm
  rw [wattMajorant_eq_core]
  apply hnorm.trans
  have hcore := core_ge_HCRV hp hΔ hΔ₁
  have hcore₀ : 0 ≤ core p Δ := (by positivity : 0 ≤ p.H*p.C*p.R*p.V).trans hcore
  have hloss : (totalSize p)^η ≤ (totalSize p)^(20*η) :=
    Real.rpow_le_rpow_of_exponent_le (totalSize_ge_one hp) (by linarith)
  calc
    _ ≤ C*core p Δ*(totalSize p)^η :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcore hC) (by positivity)
    _ ≤ C*core p Δ*(totalSize p)^(20*η) := mul_le_mul_of_nonneg_left hloss (mul_nonneg hC hcore₀)
    _ = _ := by ring

end
end Watt41
end DivisorProof
