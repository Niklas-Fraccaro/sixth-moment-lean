import SixthMoment.Arithmetic.Watt.BlockBound
import SixthMoment.Arithmetic.Watt.PoissonIntegral


namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

def integrationRange (p : WattScales) : Set ℝ :=
  Icc (p.V/(2*p.S*p.P)) (4*p.V/(p.S*p.P))

theorem blockIntegrand_continuous {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (A : ℝ) (i j k : ℕ) (τ σ : ℤ) :
    Continuous (blockIntegrand p A i j k τ σ a bc u₀ u₁ γ) := by
  have hγ (r s : ℕ) (t : ℝ) : Continuous (fun y => curveWeight γ y r s t) :=
    (hw.gamma_smooth r s).continuous.comp
      (((continuous_const.mul continuous_id).mul continuous_const).prodMk continuous_const)
  unfold blockIntegrand complexWeightedSum complexInnerSum
  apply continuous_finsetSum
  intro rs _
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro h _
  apply continuous_finsetSum
  intro c _
  apply continuous_finsetSum
  intro l _
  apply Continuous.mul
  · unfold oscillatoryBlock
    exact continuous_const.mul (continuous_const.mul
      (continuous_ePhase.comp ((continuous_const.mul continuous_id).mul continuous_const)))
  · apply continuous_finsetSum
    intro t _
    exact (hγ rs.1 rs.2 t).mul continuous_const

theorem blockIntegrand_zero_of_outside {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (hP : 0 < p.P) (hS : 0 < p.S)
    (A : ℝ) (i j k : ℕ) (τ σ : ℤ) {y : ℝ} (hy : y ∉ integrationRange p) :
    blockIntegrand p A i j k τ σ a bc u₀ u₁ γ y = 0 := by
  unfold blockIntegrand complexWeightedSum
  apply sum_eq_zero
  intro rs hrs
  have hs : rs.2 ∈ dyadicRange p.S := (mem_product.mp (mem_filter.mp hrs).1).2
  have hzero (t : ℝ) : curveWeight γ y rs.1 rs.2 t = 0 := by
    by_contra hn
    exact hy (gamma_curve_y_support hw hV hP hS rs.1 hs t (subset_tsupport _ hn))
  simp only [complexInnerSum,hzero,zero_mul,sum_const_zero,mul_zero]

theorem blockIntegrand_integrable {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (hP : 0 < p.P) (hS : 0 < p.S)
    (A : ℝ) (i j k : ℕ) (τ σ : ℤ) :
    Integrable (blockIntegrand p A i j k τ σ a bc u₀ u₁ γ) :=
  (blockIntegrand_continuous hw A i j k τ σ).integrable_of_hasCompactSupport
    (HasCompactSupport.intro isCompact_Icc
      (fun _y hy => blockIntegrand_zero_of_outside hw hV hP hS A i j k τ σ hy))

theorem integrationRange_properties {p : WattScales} {E y : ℝ}
    (hV : 0 < p.V) (hP : 0 < p.P) (hS : 0 < p.S) (hE : 0 ≤ E)
    (hy : y ∈ integrationRange p) : 0 < y ∧ dualLength p E*|y| ≤ 4*E := by
  have hyp : 0 < y := lt_of_lt_of_le (by positivity : 0 < p.V/(2*p.S*p.P)) hy.1
  refine ⟨hyp,?_⟩
  have hupper : (p.S*p.P)*y ≤ 4*p.V := by
    have hb := (le_div_iff₀ (mul_pos hS hP)).mp hy.2
    nlinarith
  calc
    _ = ((p.S*p.P)*y)/p.V*E := by rw [dualLength,abs_of_pos hyp]; ring
    _ ≤ 4*E := mul_le_mul_of_nonneg_right ((div_le_iff₀ hV).mpr hupper) hE

theorem norm_integral_le_Icc {f : ℝ → ℂ} {a b B : ℝ}
    (hab : a ≤ b) (hz : ∀ y, y ∉ Icc a b → f y = 0)
    (hb : ∀ y ∈ Icc a b, ‖f y‖ ≤ B) : ‖∫ y : ℝ, f y‖ ≤ B*(b-a) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  simpa only [Real.volume_real_Icc_of_le hab] using
    norm_setIntegral_le_of_norm_le_const (μ := volume) isCompact_Icc.measure_lt_top hb

end
end Watt41

noncomputable section

theorem Watt41.completedBlock_integral_bound (hWatt : Watt41) {ε : ℝ} (hε : 0 < ε)
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
          ‖∫ y : ℝ, Watt41.blockIntegrand p (Watt41.dualLength p E) i j k τ σ a bc u₀ u₁ γ y‖ ≤
            (C*Watt41.majorant (Watt41.blockScales p (Watt41.dualLength p E) i j k) (Δ/E) ε)*
              (4*p.V/(p.S*p.P)-p.V/(2*p.S*p.P)) := by
  obtain ⟨C,F,hC,hF,hbound⟩ := hWatt.completedBlock_bound hε b hb g hg
  refine ⟨C,F,hC,hF,?_⟩
  intro p Δ E a bc u₀ u₁ γ hp hΔ hΔ₁ hE hw hlarge hfirst hsecond i j k τ σ hi hj hk hτ hσ
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  apply Watt41.norm_integral_le_Icc
  · have hl : 0 < p.V/(2*p.S*p.P) := by positivity
    have he : 4*p.V/(p.S*p.P) = 8*(p.V/(2*p.S*p.P)) := by ring
    rw [he]
    linarith
  · intro y hy
    exact Watt41.blockIntegrand_zero_of_outside hw hV hP hS _ i j k τ σ hy
  · intro y hy
    have hys := Watt41.integrationRange_properties hV hP hS (by linarith : 0 ≤ E) hy
    exact hbound p Δ E a bc u₀ u₁ γ hp hΔ hΔ₁ hE hw hlarge hfirst hsecond
      i j k τ σ hi hj hk hτ hσ y hys.1 hys.2

end
end DivisorProof
