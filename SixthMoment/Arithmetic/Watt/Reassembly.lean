import SixthMoment.Arithmetic.Watt.FrequencyBounds

namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 4000000

theorem positiveRange_mono {A B : ℝ} (h : A ≤ B) : positiveRange A ⊆ positiveRange B := by
  intro n hn
  obtain ⟨hn,hA⟩ := mem_positiveRange.mp hn
  exact mem_positiveRange.mpr ⟨hn,hA.trans h⟩

theorem sum_supported_range {A B : ℝ} (hAB : A ≤ B) (w : ℝ → ℂ)
    (hw : tsupport w ⊆ Icc (A/2) A) (F : ℕ → ℂ) :
    (∑ n ∈ positiveRange B, w n*F n) = ∑ n ∈ positiveRange A, w n*F n := by
  symm
  apply sum_subset (positiveRange_mono hAB)
  intro n hn hna
  have hz : w n = 0 := by
    by_contra hne
    have hbound := hw (subset_tsupport _ hne)
    exact hna (mem_positiveRange.mpr ⟨(mem_positiveRange.mp hn).1,hbound.2⟩)
  rw [hz,zero_mul]

def tripleSum (H K L : ℝ) (u v w : ℝ → ℂ) (F : ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ h ∈ positiveRange H, u h*∑ k ∈ positiveRange K, v k*∑ l ∈ positiveRange L, w l*F h k l

theorem tripleSum_shrink {H K L H' K' L' : ℝ} (hH : H' ≤ H) (hK : K' ≤ K) (hL : L' ≤ L)
    (u v w : ℝ → ℂ) (hu : tsupport u ⊆ Icc (H'/2) H')
    (hv : tsupport v ⊆ Icc (K'/2) K') (hw : tsupport w ⊆ Icc (L'/2) L')
    (F : ℕ → ℕ → ℕ → ℂ) :
    tripleSum H K L u v w F = tripleSum H' K' L' u v w F := by
  unfold tripleSum
  rw [sum_supported_range hH u hu]
  apply sum_congr rfl
  intro h _
  congr 1
  rw [sum_supported_range hK v hv]
  apply sum_congr rfl
  intro k _
  congr 1
  exact sum_supported_range hL w hw (F h k)

theorem tripleSum_partition {H K L : ℝ} (hH : 0 < H) (hK : 0 < K) (hL : 0 < L)
    {NH NK NL : ℕ} (hfH : blockScale H NH < 4/3) (hfK : blockScale K NK < 4/3)
    (hfL : blockScale L NL < 4/3) (u v w : ℝ → ℂ)
    (hu : tsupport u ⊆ Icc (1/2) H) (hv : tsupport v ⊆ Icc (1/2) K)
    (hw : tsupport w ⊆ Icc (1/2) L) (F : ℕ → ℕ → ℕ → ℂ) :
    tripleSum H K L u v w F =
      ∑ i ∈ range (NH+1), ∑ j ∈ range (NK+1), ∑ n ∈ range (NL+1),
        tripleSum (blockScale H i) (blockScale K j) (blockScale L n)
          (weightedBlock u H i) (weightedBlock v K j) (weightedBlock w L n) F := by
  have heq : tripleSum H K L u v w F =
      ∑ h ∈ positiveRange H, ∑ k ∈ positiveRange K, ∑ l ∈ positiveRange L,
      ∑ i ∈ range (NH+1), ∑ j ∈ range (NK+1), ∑ n ∈ range (NL+1),
        weightedBlock u H i h*weightedBlock v K j k*weightedBlock w L n l*F h k l := by
    unfold tripleSum
    simp only [mul_sum]
    apply sum_congr rfl
    intro h hh
    apply sum_congr rfl
    intro k hk
    apply sum_congr rfl
    intro l hl
    have hhp : (1 : ℝ) ≤ h := by exact_mod_cast (mem_positiveRange.mp hh).1
    have hkp : (1 : ℝ) ≤ k := by exact_mod_cast (mem_positiveRange.mp hk).1
    have hlp : (1 : ℝ) ≤ l := by exact_mod_cast (mem_positiveRange.mp hl).1
    rw [← sum_weightedBlocks hH hfH hhp (u := u),← sum_weightedBlocks hK hfK hkp (u := v),
      ← sum_weightedBlocks hL hfL hlp (u := w)]
    simp only [sum_mul,mul_sum,mul_assoc]
    simp_rw [sum_comm (s := range (NK+1)) (t := range (NH+1)),
      sum_comm (s := range (NL+1)) (t := range (NH+1)),
      sum_comm (s := range (NL+1)) (t := range (NK+1))]
  rw [heq]
  simp_rw [sum_comm (s := positiveRange L) (t := range (NH+1)),
    sum_comm (s := positiveRange K) (t := range (NH+1)),
    sum_comm (s := positiveRange H) (t := range (NH+1)),
    sum_comm (s := positiveRange L) (t := range (NK+1)),
    sum_comm (s := positiveRange K) (t := range (NK+1)),
    sum_comm (s := positiveRange H) (t := range (NK+1)),
    sum_comm (s := positiveRange L) (t := range (NL+1)),
    sum_comm (s := positiveRange K) (t := range (NL+1)),
    sum_comm (s := positiveRange H) (t := range (NL+1))]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro n _
  have hs := tripleSum_shrink (blockScale_le hH.le i) (blockScale_le hK.le j) (blockScale_le hL.le n)
    (weightedBlock u H i) (weightedBlock v K j) (weightedBlock w L n)
    (weightedBlock_support hH hu i) (weightedBlock_support hK hv j) (weightedBlock_support hL hw n) F
  simpa only [tripleSum,mul_sum,mul_assoc] using hs

def smoothedSum (p : WattScales) (A : ℝ) (positive : Bool) (τ : ℤ)
    (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ) : ℂ :=
  ∑ rs ∈ pairRange (completedScales p 1), a rs.1*bc rs.2*
    tripleSum p.H p.C A u₀ u₁ (positiveFrequencyProfile (A/2))
      (fun h c l => ∑ t ∈ (positiveRange p.P).filter (fun t => t.Coprime rs.1),
        completedTerm p γ positive h c rs.1 rs.2 t (τ*l))

theorem smoothedSum_eq_blocks {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ A : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hH : 0 < p.H) (hK : 0 < p.C) (hA : 0 < A) {NH NK NA : ℕ}
    (hfH : blockScale p.H NH < 4/3) (hfK : blockScale p.C NK < 4/3)
    (hfA : blockScale A NA < 4/3) (positive : Bool) (τ : ℤ) :
    smoothedSum p A positive τ a bc u₀ u₁ γ =
      ∑ i ∈ range (NH+1), ∑ j ∈ range (NK+1), ∑ n ∈ range (NA+1),
        completedBlockSum p A i j n positive τ a bc u₀ u₁ γ := by
  have hω : tsupport (positiveFrequencyProfile (A/2)) ⊆ Icc (1/2) A := by
    convert positiveFrequencyProfile_support (by positivity : 0 < A/2) using 1
    ring
  unfold smoothedSum
  simp_rw [tripleSum_partition hH hK hA hfH hfK hfA u₀ u₁ (positiveFrequencyProfile (A/2))
    hw.support₀ hw.support₁ hω,mul_sum]
  simp_rw [sum_comm (s := pairRange (completedScales p 1)) (t := range (NH+1)),
    sum_comm (s := pairRange (completedScales p 1)) (t := range (NK+1)),
    sum_comm (s := pairRange (completedScales p 1)) (t := range (NA+1))]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro n _
  simp only [completedBlockSum,tripleSum,mul_sum,mul_assoc,blockScales,completedScales,pairRange]

theorem smoothedSum_eq_frequency_sum (p : WattScales) {A : ℝ} (_hA : 0 < A)
    (positive : Bool) (τ : ℤ) (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
    (γ : ℕ → ℕ → ℝ → ℝ → ℂ) :
    smoothedSum p A positive τ a bc u₀ u₁ γ =
      ∑ l ∈ positiveRange A, (sourceCutoff ((l : ℝ)/(A/2)) : ℂ)*
        frequencySum p a bc u₀ u₁ γ positive (τ*l) := by
  unfold smoothedSum frequencySum pairFrequencySum tripleSum
  simp_rw [mul_sum]
  simp_rw [sum_comm (s := positiveRange p.C) (t := positiveRange A),
    sum_comm (s := positiveRange p.H) (t := positiveRange A),
    sum_comm (s := pairRange (completedScales p 1)) (t := positiveRange A)]
  apply sum_congr rfl
  intro l hl
  rw [positiveFrequencyProfile_nat (mem_positiveRange.mp hl).1]
  apply sum_congr rfl
  intro rs _
  apply sum_congr rfl
  intro h _
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro t _
  ring

theorem blockScale_ge_final {A : ℝ} (hA : 0 ≤ A) {N i : ℕ}
    (hN : 1 ≤ blockScale A N) (hi : i ∈ range (N+1)) : 1 ≤ blockScale A i :=
  hN.trans (blockScale_antitone hA (Nat.le_of_lt_succ (mem_range.mp hi)))

end
end Watt41
end DivisorProof
