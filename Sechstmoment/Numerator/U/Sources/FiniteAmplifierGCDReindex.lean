import Sechstmoment.Numerator.U.ZeroModes.Contour.LargeShift
import Sechstmoment.Numerator.U.ZeroModes.Transforms.DiagonalNativeSummation

/-! Exact finite original amplifier gcd decomposition, including the
actual two independent native upper bounds. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03FinitePrimitiveAmplifierGrid (N₁ N₂ : ℕ) : Finset (Σ _g : ℕ,ℕ×ℕ) :=
  (Finset.Icc 1 (min N₁ N₂)).sigma (fun g =>
    ((Finset.Icc 1 (N₁/g)).product (Finset.Icc 1 (N₂/g))).filter
      (fun p => p.1.Coprime p.2))

theorem a03FinitePrimitiveAmplifierGrid_mem (N₁ N₂ : ℕ) (x : Σ _g : ℕ,ℕ×ℕ) :
    x∈a03FinitePrimitiveAmplifierGrid N₁ N₂ ↔
      (1≤x.1 ∧ x.1≤min N₁ N₂) ∧
      ((1≤x.2.1 ∧ x.2.1≤N₁/x.1) ∧ (1≤x.2.2 ∧ x.2.2≤N₂/x.1)) ∧
      x.2.1.Coprime x.2.2 := by
  simp [a03FinitePrimitiveAmplifierGrid,Finset.mem_sigma,Finset.mem_filter,Finset.mem_product,
    Finset.mem_Icc,and_assoc]

theorem a03FinitePrimitiveAmplifierGrid_gcd {N₁ N₂ : ℕ} {x : Σ _g : ℕ,ℕ×ℕ}
    (hx : x∈a03FinitePrimitiveAmplifierGrid N₁ N₂) :
    Nat.gcd (x.1*x.2.1) (x.1*x.2.2)=x.1 := by
  have h := (a03FinitePrimitiveAmplifierGrid_mem N₁ N₂ x).mp hx
  rw [Nat.gcd_mul_left,h.2.2.gcd_eq_one,mul_one]

theorem a03FiniteAmplifier_gcd_reindex (N₁ N₂ : ℕ) (F : ℕ→ℕ→ℕ→ℂ) :
    (∑ g∈Finset.Icc 1 (min N₁ N₂),∑ m∈Finset.Icc 1 (N₁/g),∑ n∈Finset.Icc 1 (N₂/g),
      if m.Coprime n then F g m n else 0)=
      ∑ m∈Finset.Icc 1 N₁,∑ n∈Finset.Icc 1 N₂,
        F (Nat.gcd m n) (m/Nat.gcd m n) (n/Nat.gcd m n) := by
  have hsum : (∑ x∈a03FinitePrimitiveAmplifierGrid N₁ N₂,F x.1 x.2.1 x.2.2)=
      ∑ g∈Finset.Icc 1 (min N₁ N₂),∑ m∈Finset.Icc 1 (N₁/g),∑ n∈Finset.Icc 1 (N₂/g),
        if m.Coprime n then F g m n else 0 := by
    unfold a03FinitePrimitiveAmplifierGrid
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro g _
    rw [Finset.sum_filter]
    change (∑ p∈(Finset.Icc 1 (N₁/g)).product (Finset.Icc 1 (N₂/g)),
      if p.1.Coprime p.2 then F g p.1 p.2 else 0)=_
    exact Finset.sum_product _ _ _
  rw [←hsum]
  change _=∑ m∈Finset.Icc 1 N₁,∑ n∈Finset.Icc 1 N₂,
    (fun p : ℕ×ℕ => F (Nat.gcd p.1 p.2) (p.1/Nat.gcd p.1 p.2) (p.2/Nat.gcd p.1 p.2)) (m,n)
  rw [←Finset.sum_product (Finset.Icc 1 N₁) (Finset.Icc 1 N₂)
    (fun p : ℕ×ℕ => F (Nat.gcd p.1 p.2) (p.1/Nat.gcd p.1 p.2) (p.2/Nat.gcd p.1 p.2))]
  apply Finset.sum_bij (fun x _ => (x.1*x.2.1,x.1*x.2.2))
  · intro x hx
    have h := (a03FinitePrimitiveAmplifierGrid_mem N₁ N₂ x).mp hx
    apply Finset.mem_product.mpr
    have hg : 0<x.1 := by omega
    exact ⟨Finset.mem_Icc.mpr ⟨by nlinarith [h.1.1,h.2.1.1.1],
      by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hg).mp h.2.1.1.2⟩,
      Finset.mem_Icc.mpr ⟨by nlinarith [h.1.1,h.2.1.2.1],
      by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hg).mp h.2.1.2.2⟩⟩
  · intro x hx y hy he
    have hg : x.1=y.1 := by
      rw [←a03FinitePrimitiveAmplifierGrid_gcd hx,←a03FinitePrimitiveAmplifierGrid_gcd hy]
      exact congrArg (fun p : ℕ×ℕ => Nat.gcd p.1 p.2) he
    have hxp := ((a03FinitePrimitiveAmplifierGrid_mem N₁ N₂ x).mp hx).1.1
    have hm : x.2.1=y.2.1 := by
      have h := congrArg Prod.fst he
      rw [←hg] at h
      exact Nat.eq_of_mul_eq_mul_left (by omega) h
    have hn : x.2.2=y.2.2 := by
      have h := congrArg Prod.snd he
      rw [←hg] at h
      exact Nat.eq_of_mul_eq_mul_left (by omega) h
    cases x with | mk d p =>
      cases y with | mk e q =>
        dsimp only at hg hm hn
        subst e
        congr 1
        exact Prod.ext hm hn
  · intro p hp
    have hm := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
    have hn := Finset.mem_Icc.mp (Finset.mem_product.mp hp).2
    let d := Nat.gcd p.1 p.2
    have hd : 0<d := Nat.gcd_pos_of_pos_left _ (by omega)
    have hdl : d≤p.1 := Nat.gcd_le_left _ (by omega)
    have hdr : d≤p.2 := Nat.gcd_le_right _ (by omega)
    have hmexact : d*(p.1/d)=p.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have hnexact : d*(p.2/d)=p.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    refine ⟨⟨d,(p.1/d,p.2/d)⟩,?_,?_⟩
    · apply (a03FinitePrimitiveAmplifierGrid_mem N₁ N₂ _).mpr
      change (1≤d ∧ d≤min N₁ N₂) ∧
        ((1≤p.1/d ∧ p.1/d≤N₁/d) ∧ (1≤p.2/d ∧ p.2/d≤N₂/d)) ∧
        (p.1/d).Coprime (p.2/d)
      exact ⟨⟨hd,le_min (hdl.trans hm.2) (hdr.trans hn.2)⟩,
        ⟨⟨Nat.div_pos hdl hd,Nat.div_le_div_right hm.2⟩,
          ⟨Nat.div_pos hdr hd,Nat.div_le_div_right hn.2⟩⟩,
        Nat.coprime_div_gcd_div_gcd hd⟩
    · exact Prod.ext hmexact hnexact
  · intro x hx
    have h := (a03FinitePrimitiveAmplifierGrid_mem N₁ N₂ x).mp hx
    rw [a03FinitePrimitiveAmplifierGrid_gcd hx]
    simp only [Nat.mul_div_cancel_left _ (by omega : 0<x.1)]

end
end Sechstmoment
