import Sechstmoment.Arithmetic.Watt.FiniteCompletion

/-! The literal finite Watt sum is identified with its absolutely convergent
frequency expansion, retaining the arithmetic restrictions. -/

namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 2000000

theorem sum_four_swap_pairs (A B C D : Finset ℕ) (F : ℕ → ℕ → ℕ → ℕ → ℂ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, F a b c d) =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, F a b c d := by
  calc
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ b ∈ B, ∑ d ∈ D, F a b c d := by
      apply sum_congr rfl
      intro a _
      exact sum_comm
    _ = ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, ∑ d ∈ D, F a b c d := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro c _
      calc
        _ = ∑ a ∈ A, ∑ d ∈ D, ∑ b ∈ B, F a b c d := by
          apply sum_congr rfl
          intro a _
          exact sum_comm
        _ = _ := sum_comm

def pairFourierSum (p : WattScales) (u₀ u₁ : ℝ → ℂ)
    (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (positive : Bool) (r s : ℕ) : ℂ :=
  ∑ h ∈ positiveRange p.H, ∑ k ∈ positiveRange p.C, u₀ h*u₁ k*
    ∑ t ∈ (positiveRange p.P).filter (fun t => t.Coprime r),
      ∑' l : ℤ, completedTerm p γ positive h k r s t l

theorem weightedWattSum_eq_pair_sums {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (positive : Bool) :
    weightedWattSum positive p a bc u₀ u₁ γ =
      ∑ r ∈ positiveRange p.R, ∑ s ∈ positiveRange p.S,
        if r.Coprime s then a r*bc s*pairFourierSum p u₀ u₁ γ positive r s else 0 := by
  rw [weightedWattSum_eq_fourier_sums hw hV,sum_four_swap_pairs]
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s _
  by_cases hrs : r.Coprime s
  · rw [ite_eq_left hrs]
    unfold pairFourierSum
    simp only [mul_sum]
    apply sum_congr rfl
    intro h _
    apply sum_congr rfl
    intro k _
    rw [sum_filter]
    apply sum_congr rfl
    intro t _
    by_cases ht : t.Coprime r
    · have hrt := hrs.mul_right ht.symm
      rw [ite_eq_left hrt,ite_eq_left ht]
      ring
    · have hrt : ¬ r.Coprime (s*t) := fun h => ht h.symm.coprime_mul_left
      rw [ite_eq_right hrt,ite_eq_right ht]
      ring
  · rw [ite_eq_right hrs]
    apply sum_eq_zero
    intro h _
    apply sum_eq_zero
    intro k _
    apply sum_eq_zero
    intro t _
    have hrt : ¬ r.Coprime (s*t) := fun h => hrs h.symm.coprime_mul_right.symm
    rw [ite_eq_right hrt,mul_zero]

/-- The outer coefficients enforce exactly the dyadic pair ranges of Watt. -/
theorem weightedWattSum_eq_dyadic_pair_sums {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (positive : Bool) :
    weightedWattSum positive p a bc u₀ u₁ γ =
      ∑ r ∈ dyadicRange p.R, ∑ s ∈ dyadicRange p.S,
        if r.Coprime s then a r*bc s*pairFourierSum p u₀ u₁ γ positive r s else 0 := by
  rw [weightedWattSum_eq_pair_sums hw hV]
  calc
    _ = ∑ r ∈ dyadicRange p.R, ∑ s ∈ positiveRange p.S,
        if r.Coprime s then a r*bc s*pairFourierSum p u₀ u₁ γ positive r s else 0 := by
      symm
      apply sum_subset (filter_subset _ _)
      intro r hr hrd
      have hzero : a r = 0 := by
        apply hw.alpha_support
        intro hmem
        exact hrd (mem_filter.mpr ⟨hr,hmem.1⟩)
      simp only [hzero,zero_mul,ite_self,sum_const_zero]
    _ = _ := by
      apply sum_congr rfl
      intro r _
      symm
      apply sum_subset (filter_subset _ _)
      intro s hs hsd
      have hzero : bc s = 0 := by
        apply hw.beta_support
        intro hmem
        exact hsd (mem_filter.mpr ⟨hs,hmem.1⟩)
      simp only [hzero,mul_zero,zero_mul,ite_self]

def pairFrequencySum (p : WattScales) (u₀ u₁ : ℝ → ℂ)
    (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (positive : Bool) (r s : ℕ) (l : ℤ) : ℂ :=
  ∑ h ∈ positiveRange p.H, ∑ k ∈ positiveRange p.C, u₀ h*u₁ k*
    ∑ t ∈ (positiveRange p.P).filter (fun t => t.Coprime r),
      completedTerm p γ positive h k r s t l

theorem pairFrequencySum_summable {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (positive : Bool) (r : ℕ) {s : ℕ} (hs : 0 < s) :
    Summable (pairFrequencySum p u₀ u₁ γ positive r s) := by
  apply summable_sum
  intro h _
  apply summable_sum
  intro k _
  apply Summable.mul_left
  apply summable_sum
  intro t ht
  exact completedTerm_summable hw positive h k r hs (Finset.mem_Icc.mp (mem_filter.mp ht).1).1

theorem pairFourierSum_eq_tsum {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (positive : Bool) (r : ℕ) {s : ℕ} (hs : 0 < s) :
    pairFourierSum p u₀ u₁ γ positive r s =
      ∑' l : ℤ, pairFrequencySum p u₀ u₁ γ positive r s l := by
  have hterm (h k t : ℕ) (ht : t ∈ (positiveRange p.P).filter (fun t => t.Coprime r)) :=
    completedTerm_summable hw positive h k r hs (Finset.mem_Icc.mp (mem_filter.mp ht).1).1
  have htSum (h k : ℕ) : Summable (fun l : ℤ =>
      ∑ t ∈ (positiveRange p.P).filter (fun t => t.Coprime r),
        completedTerm p γ positive h k r s t l) := summable_sum (hterm h k)
  unfold pairFourierSum pairFrequencySum
  rw [Summable.tsum_finsetSum (fun h _ => summable_sum (fun k _ => (htSum h k).mul_left _))]
  apply sum_congr rfl
  intro h _
  rw [Summable.tsum_finsetSum (fun k _ => (htSum h k).mul_left _)]
  apply sum_congr rfl
  intro k _
  rw [tsum_mul_left,Summable.tsum_finsetSum (hterm h k)]

theorem weightedWattSum_eq_completed_pairs {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (positive : Bool) :
    weightedWattSum positive p a bc u₀ u₁ γ =
      ∑ rs ∈ pairRange (completedScales p 1),
        a rs.1*bc rs.2*pairFourierSum p u₀ u₁ γ positive rs.1 rs.2 := by
  change _ = ∑ rs ∈ ((dyadicRange p.R) ×ˢ (dyadicRange p.S)).filter
      (fun rs => rs.1.Coprime rs.2), _
  rw [sum_filter,sum_product]
  exact weightedWattSum_eq_dyadic_pair_sums hw hV positive

def frequencySum (p : WattScales) (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
    (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (positive : Bool) (l : ℤ) : ℂ :=
  ∑ rs ∈ pairRange (completedScales p 1),
    a rs.1*bc rs.2*pairFrequencySum p u₀ u₁ γ positive rs.1 rs.2 l

theorem frequencySum_summable {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (positive : Bool) : Summable (frequencySum p a bc u₀ u₁ γ positive) := by
  apply summable_sum
  intro rs hrs
  have hs : 0 < rs.2 :=
    (Finset.mem_Icc.mp (mem_filter.mp (mem_product.mp (mem_filter.mp hrs).1).2).1).1
  exact (pairFrequencySum_summable hw positive rs.1 hs).mul_left _

/-- Every finite/infinite interchange in the completed six-variable sum. -/
theorem weightedWattSum_eq_tsum {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (positive : Bool) :
    weightedWattSum positive p a bc u₀ u₁ γ =
      ∑' l : ℤ, frequencySum p a bc u₀ u₁ γ positive l := by
  unfold frequencySum
  have hsum (rs : ℕ × ℕ) (hrs : rs ∈ pairRange (completedScales p 1)) :=
    (pairFrequencySum_summable hw positive rs.1
      (Finset.mem_Icc.mp (mem_filter.mp (mem_product.mp (mem_filter.mp hrs).1).2).1).1).mul_left
        (a rs.1*bc rs.2)
  rw [weightedWattSum_eq_completed_pairs hw hV,Summable.tsum_finsetSum hsum]
  apply sum_congr rfl
  intro rs hrs
  have hs : 0 < rs.2 :=
    (Finset.mem_Icc.mp (mem_filter.mp (mem_product.mp (mem_filter.mp hrs).1).2).1).1
  rw [pairFourierSum_eq_tsum hw positive rs.1 hs,tsum_mul_left]

/-- The zero mode and the two signed positive-frequency series, exactly. -/
theorem weightedWattSum_eq_zero_add_signed_series {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (positive : Bool) :
    weightedWattSum positive p a bc u₀ u₁ γ =
      frequencySum p a bc u₀ u₁ γ positive 0+
        (∑' l : ℕ+, frequencySum p a bc u₀ u₁ γ positive l)+
        ∑' l : ℕ+, frequencySum p a bc u₀ u₁ γ positive (-l) := by
  rw [weightedWattSum_eq_tsum hw hV]
  exact tsum_int_eq_zero_add_tsum_pnat (frequencySum_summable hw positive)

/-- The exact finite-frequency truncation error for the original Watt sum. -/
theorem weightedWattSum_fourier_truncation {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (positive : Bool) (L : ℝ) :
    weightedWattSum positive p a bc u₀ u₁ γ-
      (∑ l ∈ frequencySet L, frequencySum p a bc u₀ u₁ γ positive l) =
        ∑' l : ℤ, if L < |(l : ℝ)| then frequencySum p a bc u₀ u₁ γ positive l else 0 := by
  rw [weightedWattSum_eq_tsum hw hV]
  exact fourier_split_finite (frequencySum_summable hw positive) L

end
end Watt41
end DivisorProof
