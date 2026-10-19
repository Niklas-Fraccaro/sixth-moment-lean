import Sechstmoment.Numerator.U.ZeroModes.Transforms.CosineGapMellinSeriesBase

/-! Absolute mass of every actual positive gcd gap, retaining its
arithmetic gcd coefficient and the actual T*d*h/X frequency. -/
namespace Sechstmoment.Source
open Complex Real Set Filter MeasureTheory
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1000000

def a03NativeGCDFrequencyMassTerm (T X d : ℝ) (h : ℕ) : ℝ :=
  d/(1+T*d*((h:ℝ)+1)/X)^2

theorem a03NativeGCDFrequencyMassTerm_bound {T X d : ℝ}
    (hT : 0<T) (hX : 0<X) (hd : 1≤d) (h : ℕ) :
    a03NativeGCDFrequencyMassTerm T X d h≤(X/T)^2*((h:ℝ)+1)^(-(2:ℝ)) := by
  have hdp : 0<d := zero_lt_one.trans_le hd
  have hHp : (0:ℝ)<(h:ℝ)+1 := by positivity
  have hξ : 0<T*d*((h:ℝ)+1)/X := by positivity
  unfold a03NativeGCDFrequencyMassTerm
  calc
    _≤d/(T*d*((h:ℝ)+1)/X)^2 :=
      div_le_div_of_nonneg_left hdp.le (pow_pos hξ 2) (by nlinarith)
    _=((X/T)^2*((h:ℝ)+1)^(-(2:ℝ)))/d := by
      rw [Real.rpow_neg hHp.le,Real.rpow_ofNat]
      field_simp
    _≤(X/T)^2*((h:ℝ)+1)^(-(2:ℝ)) :=
      div_le_self (by positivity) hd

theorem a03NativeGCDFrequencyMass_summable_bound {T X d : ℝ}
    (hT : 0<T) (hX : 0<X) (hd : 1≤d) :
    Summable (a03NativeGCDFrequencyMassTerm T X d) ∧
      (∑' h : ℕ,a03NativeGCDFrequencyMassTerm T X d h)≤
        (X/T)^2*(∑' h : ℕ,((h:ℝ)+1)^(-(2:ℝ))) := by
  have hmajor := (a03GapPower_summable (by norm_num : (1:ℝ)<2)).mul_left ((X/T)^2)
  have hn (h : ℕ) : 0≤a03NativeGCDFrequencyMassTerm T X d h := by
    dsimp [a03NativeGCDFrequencyMassTerm]
    exact div_nonneg (zero_le_one.trans hd) (sq_nonneg _)
  have hs := hmajor.of_nonneg_of_le hn (a03NativeGCDFrequencyMassTerm_bound hT hX hd)
  refine ⟨hs,?_⟩
  exact (hs.tsum_le_tsum (a03NativeGCDFrequencyMassTerm_bound hT hX hd) hmajor).trans_eq
    (tsum_mul_left)

theorem a03NativeGCDFrequencyMass_actual_gcd {a b m n : ℕ} (ha : 0<a) (hm : 0<m)
    {T X : ℝ} (hT : 0<T) (hX : 0<X) :
    Summable (a03NativeGCDFrequencyMassTerm T X (Nat.gcd (a*m) (b*n))) ∧
      (∑' h : ℕ,a03NativeGCDFrequencyMassTerm T X (Nat.gcd (a*m) (b*n)) h)≤
        (X/T)^2*(∑' h : ℕ,((h:ℝ)+1)^(-(2:ℝ))) := by
  apply a03NativeGCDFrequencyMass_summable_bound hT hX
  exact_mod_cast Nat.gcd_pos_of_pos_left (b*n) (Nat.mul_pos ha hm)

end
end Sechstmoment.Source
