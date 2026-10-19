import Sechstmoment.Arithmetic.Watt.GlobalMajorants
import Sechstmoment.Arithmetic.Watt.SmoothSplit

namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 4000000

def aggregate (p : WattScales) (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
    (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℂ) : ℂ :=
  ∑ rs ∈ pairRange (completedScales p 1), a rs.1*bc rs.2*
    ∑ t ∈ (positiveRange p.P).filter (fun t => t.Coprime rs.1),
      ∑ h ∈ positiveRange p.H, ∑ k ∈ positiveRange p.C, u₀ h*u₁ k*F h k rs.1 rs.2 t

theorem frequencySum_eq_aggregate (p : WattScales) (positive : Bool)
    (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ) (l : ℤ) :
    frequencySum p a bc u₀ u₁ γ positive l =
      aggregate p a bc u₀ u₁ (fun h k r s t => completedTerm p γ positive h k r s t l) := by
  unfold frequencySum pairFrequencySum aggregate
  apply sum_congr rfl
  intro rs _
  congr 1
  simp only [mul_sum]
  simp_rw [sum_comm (s := positiveRange p.C) (t := (positiveRange p.P).filter (fun t => t.Coprime rs.1)),
    sum_comm (s := positiveRange p.H) (t := (positiveRange p.P).filter (fun t => t.Coprime rs.1))]

theorem aggregate_tsum (p : WattScales) (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ)
    (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℤ → ℂ)
    (hsum : ∀ h k r s t, 0 < s → 0 < t → Summable (F h k r s t)) :
    (∑' l : ℤ, aggregate p a bc u₀ u₁ (fun h k r s t => F h k r s t l)) =
      aggregate p a bc u₀ u₁ (fun h k r s t => ∑' l : ℤ, F h k r s t l) := by
  have hhks (r s t : ℕ) (hs : 0 < s) (ht : 0 < t) :=
    summable_sum (s := positiveRange p.H) (fun h _ =>
      summable_sum (s := positiveRange p.C) (fun k _ => (hsum h k r s t hs ht).mul_left (u₀ h*u₁ k)))
  have hts (r s : ℕ) (hs : 0 < s) := summable_sum
    (s := (positiveRange p.P).filter (fun t => t.Coprime r))
    (fun t ht => hhks r s t hs (mem_positiveRange.mp (mem_filter.mp ht).1).1)
  have hrs (rs : ℕ × ℕ) (hr : rs ∈ pairRange (completedScales p 1)) :=
    (hts rs.1 rs.2 (mem_dyadicRange.mp (mem_product.mp (mem_filter.mp hr).1).2).1).mul_left
      (a rs.1*bc rs.2)
  unfold aggregate
  rw [Summable.tsum_finsetSum hrs]
  apply sum_congr rfl
  intro rs hr
  have hs : 0 < rs.2 := (mem_dyadicRange.mp (mem_product.mp (mem_filter.mp hr).1).2).1
  rw [tsum_mul_left,Summable.tsum_finsetSum (fun t ht =>
    hhks rs.1 rs.2 t hs (mem_positiveRange.mp (mem_filter.mp ht).1).1)]
  congr 1
  apply sum_congr rfl
  intro t ht
  have htp := (mem_positiveRange.mp (mem_filter.mp ht).1).1
  rw [Summable.tsum_finsetSum (fun h _ => summable_sum (fun k _ =>
    (hsum h k rs.1 rs.2 t hs htp).mul_left (u₀ h*u₁ k)))]
  apply sum_congr rfl
  intro h _
  rw [Summable.tsum_finsetSum (fun k _ => (hsum h k rs.1 rs.2 t hs htp).mul_left (u₀ h*u₁ k))]
  apply sum_congr rfl
  intro k _
  exact tsum_mul_left

theorem card_positiveRange_le {A : ℝ} (hA : 0 ≤ A) : ((positiveRange A).card : ℝ) ≤ A := by
  have hc : (positiveRange A).card = ⌊A⌋₊ := by simp [positiveRange,Nat.card_Icc]
  rw [hc]
  exact Nat.floor_le hA

theorem card_dyadicRange_le {A : ℝ} (hA : 0 ≤ A) : ((dyadicRange A).card : ℝ) ≤ A := by
  apply le_trans _ (card_positiveRange_le hA)
  exact_mod_cast card_filter_le (positiveRange A) _

theorem card_pairRange_le {p : WattScales} (hR : 0 ≤ p.R) (hS : 0 ≤ p.S) :
    ((pairRange (completedScales p 1)).card : ℝ) ≤ p.R*p.S := by
  have hc : (pairRange (completedScales p 1)).card ≤ (dyadicRange p.R).card*(dyadicRange p.S).card :=
    (card_filter_le _ _).trans_eq (card_product _ _)
  have hc' : ((pairRange (completedScales p 1)).card : ℝ) ≤
      ((dyadicRange p.R).card : ℝ)*(dyadicRange p.S).card := by exact_mod_cast hc
  exact hc'.trans (mul_le_mul (card_dyadicRange_le hR) (card_dyadicRange_le hS) (Nat.cast_nonneg _) hR)

theorem norm_sum_le_scale {ι : Type*} (s : Finset ι) (F : ι → ℂ) {M B : ℝ}
    (hcard : (s.card : ℝ) ≤ M) (hB : 0 ≤ B) (hF : ∀ n ∈ s, ‖F n‖ ≤ B) :
    ‖∑ n ∈ s, F n‖ ≤ M*B := by
  calc
    _ ≤ ∑ n ∈ s, B := (norm_sum_le _ _).trans (sum_le_sum hF)
    _ = (s.card : ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard hB

theorem aggregate_fibre_bound {p : WattScales} (hp : ∀ n, 1 ≤ p.size n)
    (a bc : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ) (F : ℕ → ℕ → ℕ → ℕ → ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ n, ‖bc n‖ ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ rs ∈ pairRange (completedScales p 1),
      ∀ t ∈ (positiveRange p.P).filter (fun t => t.Coprime rs.1),
        ‖∑ h ∈ positiveRange p.H, ∑ k ∈ positiveRange p.C, u₀ h*u₁ k*F h k rs.1 rs.2 t‖ ≤ B) :
    ‖aggregate p a bc u₀ u₁ F‖ ≤ p.R*p.S*p.P*B := by
  have hR : 0 ≤ p.R := zero_le_one.trans (hp 2)
  have hS : 0 ≤ p.S := zero_le_one.trans (hp 3)
  have hP : 0 ≤ p.P := zero_le_one.trans (hp 5)
  unfold aggregate
  apply (norm_sum_le_scale _ _ (card_pairRange_le hR hS) (mul_nonneg hP hB) ?_).trans_eq
  · ring
  · intro rs hrs
    have hcard : (((positiveRange p.P).filter (fun t => t.Coprime rs.1)).card : ℝ) ≤ p.P := by
      have hc : (((positiveRange p.P).filter (fun t => t.Coprime rs.1)).card : ℝ) ≤
          ((positiveRange p.P).card : ℝ) := by exact_mod_cast card_filter_le (positiveRange p.P) _
      exact hc.trans (card_positiveRange_le hP)
    have ht := norm_sum_le_scale _ _ hcard hB (hF rs hrs)
    rw [norm_mul,norm_mul]
    have hab : ‖a rs.1‖*‖bc rs.2‖ ≤ 1 := by
      simpa only [one_mul] using mul_le_mul (ha rs.1) (hb rs.2) (norm_nonneg _) zero_le_one
    exact (mul_le_mul_of_nonneg_left ht (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hab (mul_nonneg hP hB))

theorem weight_zero_order_bound {b : ℕ → ℝ} {g : ℕ → ℕ → ℝ}
    {p : WattScales} {Δ : ℝ} {a bc : ℕ → ℂ} {u₀ u₁ : ℝ → ℂ}
    {γ : ℕ → ℕ → ℝ → ℝ → ℂ} (hw : WattWeightData b g p Δ a bc u₀ u₁ γ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (hb : 0 ≤ b 0) : ‖u₀ h*u₁ k‖ ≤ b 0^2 := by
  have h₀ := hw.derivatives 0 h (by exact_mod_cast hh)
  have h₁ := hw.derivatives 0 k (by exact_mod_cast hk)
  simp only [iteratedDeriv_zero,Nat.cast_zero,neg_zero,Real.rpow_zero,mul_one] at h₀ h₁
  rw [norm_mul]
  have ha : ‖u₀ h‖ ≤ b 0 := (le_add_of_nonneg_right (norm_nonneg _)).trans h₀
  have hc : ‖u₁ k‖ ≤ b 0 := (le_add_of_nonneg_left (norm_nonneg _)).trans h₁
  simpa only [pow_two] using mul_le_mul ha hc (norm_nonneg _) hb

end
end Watt41
end DivisorProof
