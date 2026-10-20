import SixthMoment.Arithmetic.Watt.Reassembly

namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 4000000

def cutoff (A : ℝ) (l : ℤ) : ℂ := (sourceCutoff ((l : ℝ)/(A/2)) : ℂ)

theorem cutoff_zero {A : ℝ} (hA : 0 < A) {l : ℤ} (hl : A < |(l : ℝ)|) : cutoff A l = 0 := by
  unfold cutoff
  rw [sourceCutoff_zero,Complex.ofReal_zero]
  rw [abs_div,abs_of_pos (by positivity : 0 < A/2)]
  exact (le_div_iff₀ (by positivity : 0 < A/2)).mpr (by linarith)

theorem cutoff_one {A : ℝ} (hA : 0 < A) {l : ℤ} (hl : |(l : ℝ)| ≤ A/2) : cutoff A l = 1 := by
  unfold cutoff
  rw [sourceCutoff_one,Complex.ofReal_one]
  rw [abs_div,abs_of_pos (by positivity : 0 < A/2)]
  exact (div_le_one (by positivity : 0 < A/2)).mpr hl

theorem cutoff_even (A : ℝ) (l : ℤ) : cutoff A (-l) = cutoff A l := by
  simp only [cutoff,Int.cast_neg,neg_div,sourceCutoff_even]

theorem one_sub_cutoff_norm (A : ℝ) (l : ℤ) : ‖1-cutoff A l‖ ≤ 1 := by
  have hn := sourceCutoff_nonneg ((l : ℝ)/(A/2))
  have hb : sourceCutoff ((l : ℝ)/(A/2)) ≤ 1 := (le_abs_self _).trans (sourceCutoff_norm _)
  rw [cutoff,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem cutoff_summable (f : ℤ → ℂ) {A : ℝ} (hA : 0 < A) :
    Summable (fun l => cutoff A l*f l) := by
  apply summable_of_ne_finset_zero (s := frequencySet A)
  intro l hl
  rw [cutoff_zero hA (not_le.mp (fun h => hl ((mem_frequencySet A l).mpr h))),zero_mul]

theorem smooth_tail_summable {f : ℤ → ℂ} (hf : Summable f) {A : ℝ} (hA : 0 < A) :
    Summable (fun l => (1-cutoff A l)*f l) := by
  apply (hf.sub (cutoff_summable f hA)).congr
  intro l
  ring

theorem pnat_cutoff_tsum (f : ℤ → ℂ) {A : ℝ} (hA : 0 < A) (τ : ℤ) :
    (∑' n : ℕ+, cutoff A n*f (τ*n)) =
      ∑ n ∈ positiveRange A, cutoff A n*f (τ*n) := by
  let F : ℕ → ℂ := fun n => if n = 0 then 0 else cutoff A n*f (τ*n)
  have hF₀ : F 0 = 0 := by simp only [F,ite_true]
  have hts : (∑' n : ℕ+, F n) = ∑' n : ℕ, F n := tsum_pnat_eq_tsum_of_eq_zero hF₀
  have hp : (∑' n : ℕ+, F n) = ∑' n : ℕ+, cutoff A n*f (τ*n) := by
    apply tsum_congr
    intro n
    exact ite_eq_right (Nat.ne_of_gt n.pos)
  rw [hp] at hts
  rw [hts]
  rw [tsum_eq_sum (s := positiveRange A)]
  · apply sum_congr rfl
    intro n hn
    exact ite_eq_right (Nat.ne_of_gt (mem_positiveRange.mp hn).1)
  · intro n hn
    by_cases hz : n = 0
    · simp only [F,ite_eq_left hz]
    · have hnp : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hz
      have hbound : A < (n : ℝ) := not_le.mp (fun h => hn (mem_positiveRange.mpr ⟨hnp,h⟩))
      have ha : A < |((n : ℤ) : ℝ)| := by simpa only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hbound
      simp only [F,ite_eq_right hz,cutoff_zero hA ha,zero_mul]

theorem cutoff_tsum_split (f : ℤ → ℂ) {A : ℝ} (hA : 0 < A) :
    (∑' l : ℤ, cutoff A l*f l) = f 0+
      (∑ n ∈ positiveRange A, cutoff A n*f n)+
        ∑ n ∈ positiveRange A, cutoff A n*f (-n) := by
  rw [tsum_int_eq_zero_add_tsum_pnat (cutoff_summable f hA)]
  have hz : cutoff A 0 = 1 := cutoff_one hA (by norm_num; linarith)
  rw [hz,one_mul]
  have hp := pnat_cutoff_tsum f hA 1
  have hn := pnat_cutoff_tsum f hA (-1)
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hn
  simp_rw [cutoff_even]
  rw [hp,hn]

def highSum (p : WattScales) (A : ℝ) (positive : Bool) (a bc : ℕ → ℂ)
    (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ) : ℂ :=
  ∑' l : ℤ, (1-cutoff A l)*frequencySum p a bc u₀ u₁ γ positive l

theorem weightedWattSum_smooth_split {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ A : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    (hV : 0 < p.V) (hA : 0 < A) (positive : Bool) :
    weightedWattSum positive p a bc u₀ u₁ γ = frequencySum p a bc u₀ u₁ γ positive 0+
      smoothedSum p A positive 1 a bc u₀ u₁ γ+
      smoothedSum p A positive (-1) a bc u₀ u₁ γ+highSum p A positive a bc u₀ u₁ γ := by
  let f := frequencySum p a bc u₀ u₁ γ positive
  have hf := frequencySum_summable hw positive
  rw [weightedWattSum_eq_tsum hw hV]
  have heq : (∑' l : ℤ, f l) = (∑' l : ℤ, cutoff A l*f l)+∑' l : ℤ, (1-cutoff A l)*f l := by
    rw [← (cutoff_summable f hA).tsum_add (smooth_tail_summable hf hA)]
    apply tsum_congr
    intro l
    ring
  rw [heq,cutoff_tsum_split f hA,smoothedSum_eq_frequency_sum p hA,
    smoothedSum_eq_frequency_sum p hA]
  simp only [cutoff,one_mul,neg_one_mul,highSum,f,Int.cast_natCast]

end
end Watt41
end DivisorProof
