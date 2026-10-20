import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.Divisors


namespace Sechstmoment.Source.NoDPHarmonic
open scoped BigOperators
noncomputable section

theorem sum_divisors_reindex (N : ℕ) (F : ℕ → ℕ → ℂ)
    (hcut : ∀ d m : ℕ, N < d*m → F d m = 0) :
    (∑ a ∈ Finset.Icc 1 N, ∑ d ∈ a.divisors, F d (a/d)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 N, F d m := by
  classical
  simp_rw [← Nat.sum_divisorsAntidiagonal F]
  rw [Finset.sum_sigma', ← Finset.sum_product']
  apply Finset.sum_bij_ne_zero (fun a _ _ => a.2)
  · rintro ⟨a,d,m⟩ ha _
    have ha' := Finset.mem_sigma.mp ha
    have hd := Nat.mem_divisorsAntidiagonal.mp ha'.2
    have hprod : d*m = a := hd.1
    have ha1 := (Finset.mem_Icc.mp ha'.1).1
    have hp : d*m ≠ 0 := by rw [hprod]; exact Nat.ne_of_gt ha1
    have hd0 : 0 < d := Nat.pos_of_ne_zero (left_ne_zero_of_mul hp)
    have hm0 : 0 < m := Nat.pos_of_ne_zero (right_ne_zero_of_mul hp)
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd0,
      (Nat.le_mul_of_pos_right d hm0).trans (hprod.trans_le (Finset.mem_Icc.mp ha'.1).2)⟩,
      Finset.mem_Icc.mpr ⟨hm0,
      (Nat.le_mul_of_pos_left m hd0).trans (hprod.trans_le (Finset.mem_Icc.mp ha'.1).2)⟩⟩
  · rintro ⟨a,d,m⟩ ha _ ⟨b,e,k⟩ hb _ h
    have h₁ := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp ha).2).1
    have h₂ := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hb).2).1
    have hpairs : d*m = e*k := congrArg (fun p : ℕ × ℕ => p.1*p.2) h
    have hab : a = b := h₁.symm.trans (hpairs.trans h₂)
    subst b
    cases h
    rfl
  · rintro ⟨d,m⟩ hm hn
    have hdm : d*m ≤ N := le_of_not_gt (fun h => hn (hcut d m h))
    have hd := Finset.mem_Icc.mp (Finset.mem_product.mp hm).1
    have hm' := Finset.mem_Icc.mp (Finset.mem_product.mp hm).2
    have hp : d*m ≠ 0 := mul_ne_zero (Nat.one_le_iff_ne_zero.mp hd.1)
      (Nat.one_le_iff_ne_zero.mp hm'.1)
    refine ⟨⟨d*m,d,m⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hp,hdm⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,hp⟩⟩,hn,rfl⟩
  · intro a _ _
    rfl

end
end Sechstmoment.Source.NoDPHarmonic
