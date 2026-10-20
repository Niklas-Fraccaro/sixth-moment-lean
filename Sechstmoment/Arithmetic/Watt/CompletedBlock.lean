import Sechstmoment.Arithmetic.Watt.BlockIntegral


namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem completedIntegrand_eq_watt_kernel {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (positive : Bool) (h c r : ℕ) (l : ℕ) (τ : ℤ) (y : ℝ) :
    completedIntegrand γ positive h c r s t (τ*l) y =
      ePhase ((τ : ℝ)*y*l)*(curveWeight γ y r s t*
        classicalKloostermanSum ((h : ℤ)*c*inverseRepresentative r (t*s))
          ((-phaseSign positive*τ)*l) (t*s)) := by
  unfold completedIntegrand
  have hm : phaseSign positive*(h : ℤ)*c*inverseRepresentative r (s*t) =
      phaseSign positive*((h : ℤ)*c*inverseRepresentative r (s*t)) := by ring
  rw [hm,classicalKloostermanSum_phaseSign (Nat.mul_pos hs ht)]
  have he : ((τ*(l : ℤ) : ℤ) : ℝ)*y = (τ : ℝ)*y*l := by push_cast; ring
  have hσ : -phaseSign positive*(τ*(l : ℤ)) = (-phaseSign positive*τ)*l := by ring
  rw [he,hσ]
  simp only [Nat.mul_comm s t]
  ring

def rawBlockPairIntegrand (p : WattScales) (A : ℝ) (i j k : ℕ) (positive : Bool) (τ : ℤ)
    (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (r s : ℕ) (y : ℝ) : ℂ :=
  ∑ h ∈ positiveRange (blockScale p.H i), ∑ c ∈ positiveRange (blockScale p.C j),
    ∑ l ∈ positiveRange (blockScale A k),
      weightedBlock u₀ p.H i h*weightedBlock u₁ p.C j c*
        weightedBlock (positiveFrequencyProfile (A/2)) A k l*
          ∑ t ∈ (positiveRange p.P).filter (fun t => t.Coprime r),
            completedIntegrand γ positive h c r s t (τ*l) y

def completedBlockSum (p : WattScales) (A : ℝ) (i j k : ℕ) (positive : Bool) (τ : ℤ)
    (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ) : ℂ :=
  ∑ rs ∈ pairRange (blockScales p A i j k), a rs.1*bc rs.2*
    ∑ h ∈ positiveRange (blockScale p.H i), ∑ c ∈ positiveRange (blockScale p.C j),
    ∑ l ∈ positiveRange (blockScale A k),
      weightedBlock u₀ p.H i h*weightedBlock u₁ p.C j c*
        weightedBlock (positiveFrequencyProfile (A/2)) A k l*
          ∑ t ∈ (positiveRange p.P).filter (fun t => t.Coprime rs.1),
            completedTerm p γ positive h c rs.1 rs.2 t (τ*l)

theorem blockIntegrand_eq_raw (p : WattScales) (A : ℝ) (i j k : ℕ) (positive : Bool) (τ : ℤ)
    (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (y : ℝ) :
    blockIntegrand p A i j k τ (-phaseSign positive*τ) a bc u₀ u₁ γ y =
      ∑ rs ∈ pairRange (blockScales p A i j k),
        a rs.1*bc rs.2*rawBlockPairIntegrand p A i j k positive τ u₀ u₁ γ rs.1 rs.2 y := by
  unfold blockIntegrand complexWeightedSum complexInnerSum rawBlockPairIntegrand
  apply sum_congr rfl
  intro rs hrs
  have hs : 0 < rs.2 := (mem_dyadicRange.mp (mem_product.mp (mem_filter.mp hrs).1).2).1
  congr 1
  apply sum_congr rfl
  intro h _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro l _
  simp only [mul_sum]
  apply sum_congr rfl
  intro t ht
  have htp : 0 < t := (mem_positiveRange.mp (mem_filter.mp ht).1).1
  rw [completedIntegrand_eq_watt_kernel hs htp]
  unfold oscillatoryBlock
  ring

theorem rawBlockPairIntegrand_integrable {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (hP : 0 < p.P) (hS : 0 < p.S)
    (A : ℝ) (i j k : ℕ) (positive : Bool) (τ : ℤ) (r : ℕ) {s : ℕ}
    (hs : s ∈ dyadicRange p.S) :
    Integrable (rawBlockPairIntegrand p A i j k positive τ u₀ u₁ γ r s) := by
  apply integrable_finsetSum
  intro h _
  apply integrable_finsetSum
  intro c _
  apply integrable_finsetSum
  intro l _
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro t _
  exact completedIntegrand_integrable hw hV hP hS positive h c r hs t (τ*l)

theorem rawBlockPairIntegrand_integral {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (hP : 0 < p.P) (hS : 0 < p.S)
    (A : ℝ) (i j k : ℕ) (positive : Bool) (τ : ℤ) (r : ℕ) {s : ℕ}
    (hs : s ∈ dyadicRange p.S) :
    (∫ y : ℝ, rawBlockPairIntegrand p A i j k positive τ u₀ u₁ γ r s y) =
      ∑ h ∈ positiveRange (blockScale p.H i), ∑ c ∈ positiveRange (blockScale p.C j),
      ∑ l ∈ positiveRange (blockScale A k),
        weightedBlock u₀ p.H i h*weightedBlock u₁ p.C j c*
          weightedBlock (positiveFrequencyProfile (A/2)) A k l*
            ∑ t ∈ (positiveRange p.P).filter (fun t => t.Coprime r),
              completedTerm p γ positive h c r s t (τ*l) := by
  have ht (h c l : ℕ) := integrable_finsetSum
    ((positiveRange p.P).filter (fun t => t.Coprime r))
    (fun t _ => completedIntegrand_integrable hw hV hP hS positive h c r hs t (τ*l))
  have hl (h c : ℕ) := integrable_finsetSum (positiveRange (blockScale A k))
    (fun l _ => (ht h c l).const_mul
      (weightedBlock u₀ p.H i h*weightedBlock u₁ p.C j c*
        weightedBlock (positiveFrequencyProfile (A/2)) A k l))
  unfold rawBlockPairIntegrand
  rw [integral_finsetSum _ (fun h _ => integrable_finsetSum _ (fun c _ => hl h c))]
  apply sum_congr rfl
  intro h _
  rw [integral_finsetSum _ (fun c _ => hl h c)]
  apply sum_congr rfl
  intro c _
  rw [integral_finsetSum _ (fun l _ => (ht h c l).const_mul _)]
  apply sum_congr rfl
  intro l _
  rw [integral_const_mul,integral_finsetSum _ (fun t _ =>
    completedIntegrand_integrable hw hV hP hS positive h c r hs t (τ*l))]
  simp only [completedTerm_eq_integral]

theorem completedBlockSum_eq_integral {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (hP : 0 < p.P) (hS : 0 < p.S)
    (A : ℝ) (i j k : ℕ) (positive : Bool) (τ : ℤ) :
    completedBlockSum p A i j k positive τ a bc u₀ u₁ γ =
      ∫ y : ℝ, blockIntegrand p A i j k τ (-phaseSign positive*τ) a bc u₀ u₁ γ y := by
  simp_rw [blockIntegrand_eq_raw]
  have hi (rs : ℕ × ℕ) (hrs : rs ∈ pairRange (blockScales p A i j k)) :
      Integrable (fun y => a rs.1*bc rs.2*
        rawBlockPairIntegrand p A i j k positive τ u₀ u₁ γ rs.1 rs.2 y) :=
    (rawBlockPairIntegrand_integrable hw hV hP hS A i j k positive τ rs.1
      (mem_product.mp (mem_filter.mp hrs).1).2).const_mul _
  rw [integral_finsetSum _ hi]
  unfold completedBlockSum
  apply sum_congr rfl
  intro rs hrs
  rw [integral_const_mul,rawBlockPairIntegrand_integral hw hV hP hS A i j k positive τ rs.1
    (mem_product.mp (mem_filter.mp hrs).1).2]

end
end Watt41

noncomputable section

theorem Watt41.completedFiniteBlock_bound (hWatt : Watt41) {ε : ℝ} (hε : 0 < ε)
    (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (g : ℕ → ℕ → ℝ) (hg : ∀ i j, 0 ≤ g i j) :
    ∃ C F : ℝ, 0 ≤ C ∧ 1 ≤ F ∧
      ∀ (p : WattScales) (Δ E : ℝ) (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
        (γ : ℕ → ℕ → ℝ → ℝ → ℂ),
        (∀ n, 1 ≤ p.size n) → 0 < Δ → Δ ≤ 1 → 1 ≤ E →
        WattWeightData b g p Δ a bc u₀ u₁ γ →
        F*E ≤ p.X → p.H^2*p.C ≤ (p.R*p.S)^2 →
        Watt41.dualLength p E ≤ (p.R*p.S)^2 →
        ∀ (i j k : ℕ) (positive : Bool) (τ : ℤ),
          1 ≤ Watt41.blockScale p.H i → 1 ≤ Watt41.blockScale p.C j →
          1 ≤ Watt41.blockScale (Watt41.dualLength p E) k → (τ = -1 ∨ τ = 1) →
          ‖Watt41.completedBlockSum p (Watt41.dualLength p E) i j k positive τ a bc u₀ u₁ γ‖ ≤
            (C*Watt41.majorant (Watt41.blockScales p (Watt41.dualLength p E) i j k) (Δ/E) ε)*
              (4*p.V/(p.S*p.P)-p.V/(2*p.S*p.P)) := by
  obtain ⟨C,F,hC,hF,hbound⟩ := hWatt.completedBlock_integral_bound hε b hb g hg
  refine ⟨C,F,hC,hF,?_⟩
  intro p Δ E a bc u₀ u₁ γ hp hΔ hΔ₁ hE hw hlarge hfirst hsecond i j k positive τ hi hj hk hτ
  have hS : 0 < p.S := lt_of_lt_of_le zero_lt_one (hp 3)
  have hV : 0 < p.V := lt_of_lt_of_le zero_lt_one (hp 4)
  have hP : 0 < p.P := lt_of_lt_of_le zero_lt_one (hp 5)
  have hσ : -Watt41.phaseSign positive*τ = -1 ∨ -Watt41.phaseSign positive*τ = 1 := by
    rcases hτ with rfl | rfl <;> cases positive <;> norm_num [Watt41.phaseSign]
  rw [Watt41.completedBlockSum_eq_integral hw hV hP hS]
  exact hbound p Δ E a bc u₀ u₁ γ hp hΔ hΔ₁ hE hw hlarge hfirst hsecond
    i j k τ (-Watt41.phaseSign positive*τ) hi hj hk hτ hσ

end
end DivisorProof
