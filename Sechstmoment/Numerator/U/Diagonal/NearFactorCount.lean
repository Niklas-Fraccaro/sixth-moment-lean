import Sechstmoment.Numerator.U.Diagonal.PositiveFactorCount
import Sechstmoment.Numerator.U.Diagonal.ShortFactorAverage


namespace Sechstmoment
open scoped BigOperators
open Classical

def positiveNearFactorFiber (Q u v M H : ℕ) : Finset (ℕ × ℕ) :=
  (positiveProductFactorPairs Q).filter fun p =>
    u*M ≤ v*(p.1*p.2)+H ∧ v*(p.1*p.2) ≤ u*M+H

theorem positiveNearFactorFiber_subset_short {Q u v M H : ℕ} (hv : 0<v) :
    positiveNearFactorFiber Q u v M H ⊆
      positiveShortFactorPairs Q ((u*M-H)/v) (2*H/v+1) := by
  intro p hp
  obtain ⟨hpair,hnear⟩ := Finset.mem_filter.mp hp
  obtain ⟨hp1,hp2,hprod⟩ := mem_positiveProductFactorPairs.mp hpair
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_,?_,hprod⟩
  · exact Finset.mem_Icc.mpr ⟨by omega,by nlinarith⟩
  · exact Finset.mem_Icc.mpr ⟨by omega,by nlinarith⟩
  · apply Nat.div_le_of_le_mul
    omega
  · have hupper : p.1*p.2 ≤ (u*M+H)/v :=
      (Nat.le_div_iff_mul_le hv).mpr (by simpa [Nat.mul_comm] using hnear.2)
    have hnum : u*M+H ≤ (u*M-H)+2*H := by omega
    have hdivision : (u*M+H)/v ≤ ((u*M-H)+2*H)/v :=
      Nat.div_le_div_right hnum
    have hadd : ((u*M-H)+2*H)/v ≤ (u*M-H)/v+2*H/v+1 := by
      rw [Nat.add_div hv]
      split_ifs <;> omega
    exact hupper.trans (hdivision.trans hadd)

theorem positiveNearFactorFiber_card_le_harmonic {Q u v M H K : ℕ}
    (hv : 0<v) (hQ : Q≤K^2) :
    ((positiveNearFactorFiber Q u v M H).card : ℝ) ≤
      2*((2*H/v+1 : ℕ):ℝ)*(harmonic K : ℝ)+2*K := by
  have hc : ((positiveNearFactorFiber Q u v M H).card : ℝ) ≤
      ((positiveShortFactorPairs Q ((u*M-H)/v) (2*H/v+1)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card
      (positiveNearFactorFiber_subset_short (Q:=Q) (u:=u) (M:=M) (H:=H) hv))
  exact hc.trans (positiveShortFactorPairs_card_le_harmonic hQ)

theorem positiveNearFactorFiber_card_le_real_harmonic {Q u v M H K : ℕ}
    (hv : 0<v) (hQ : Q≤K^2) :
    ((positiveNearFactorFiber Q u v M H).card : ℝ) ≤
      2*(2*(H:ℝ)/(v:ℝ)+1)*(harmonic K : ℝ)+2*K := by
  have hH : 0≤(harmonic K : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hq : ((2*H/v : ℕ):ℝ)≤2*(H:ℝ)/(v:ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hv : (0:ℝ)<v)).mpr
    exact_mod_cast Nat.div_mul_le_self (2*H) v
  exact (positiveNearFactorFiber_card_le_harmonic hv hQ).trans (by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right hq hH])

def positiveNearFactorRectangle (P Q u v H : ℕ) :
    Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  (positiveProductFactorPairs P).biUnion fun p =>
    (positiveNearFactorFiber Q u v (p.1*p.2) H).image fun q => (p,q)

theorem mem_positiveNearFactorRectangle {P Q u v H : ℕ}
    {p q : ℕ × ℕ} :
    (p,q) ∈ positiveNearFactorRectangle P Q u v H ↔
      p ∈ positiveProductFactorPairs P ∧
      q ∈ positiveNearFactorFiber Q u v (p.1*p.2) H := by
  constructor
  · intro h
    obtain ⟨a,ha,himage⟩ := Finset.mem_biUnion.mp h
    obtain ⟨b,hqb,he⟩ := Finset.mem_image.mp himage
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    exact ⟨ha,hqb⟩
  · rintro ⟨hp,hq⟩
    exact Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_image.mpr ⟨q,hq,rfl⟩⟩

theorem positiveNearFactorRectangle_card_le_harmonic {P Q u v H K : ℕ}
    (hv : 0<v) (hQ : Q≤K^2) :
    ((positiveNearFactorRectangle P Q u v H).card : ℝ) ≤
      (P:ℝ)*(harmonic P : ℝ)*
        (2*(2*(H:ℝ)/(v:ℝ)+1)*(harmonic K : ℝ)+2*K) := by
  let C : ℝ := 2*(2*(H:ℝ)/(v:ℝ)+1)*(harmonic K : ℝ)+2*K
  have hH (N : ℕ) : 0≤(harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hhK := hH K
  have hC : 0≤C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ p ∈ positiveProductFactorPairs P,
        (((positiveNearFactorFiber Q u v (p.1*p.2) H).image
          fun q => (p,q)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ = ∑ p ∈ positiveProductFactorPairs P,
        ((positiveNearFactorFiber Q u v (p.1*p.2) H).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.card_image_of_injective _ (by intro a b h; exact (Prod.mk.inj h).2)]
    _ ≤ ∑ _p ∈ positiveProductFactorPairs P, C := by
      apply Finset.sum_le_sum
      intro p hp
      exact positiveNearFactorFiber_card_le_real_harmonic hv hQ
    _ = ((positiveProductFactorPairs P).card : ℝ)*C := by simp
    _ ≤ (P:ℝ)*(harmonic P : ℝ)*C :=
      mul_le_mul_of_nonneg_right (positiveProductFactorPairs_card_le_harmonic P) hC

end Sechstmoment
