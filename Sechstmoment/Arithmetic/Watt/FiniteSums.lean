import Sechstmoment.Arithmetic.Watt.Adapters


namespace DivisorProof
namespace Watt41
open Finset Classical
open scoped BigOperators
noncomputable section

theorem sum_piFinset_succ {n : ℕ} (s : Fin (n+1) → Finset ℕ)
    (F : (Fin (n+1) → ℕ) → ℂ) :
    (∑ u ∈ Fintype.piFinset s, F u) =
      ∑ a ∈ s 0, ∑ v ∈ Fintype.piFinset (fun i : Fin n => s i.succ), F (Fin.cons a v) := by
  rw [← sum_product']
  apply sum_bij (fun u _ => (u 0, Fin.tail u))
  · intro u hu
    have hmem := Fintype.mem_piFinset.mp hu
    exact mem_product.mpr ⟨hmem 0, Fintype.mem_piFinset.mpr (fun i => hmem i.succ)⟩
  · intro u _ v _ huv
    have hhead := congrArg Prod.fst huv
    have htail := congrArg Prod.snd huv
    change u 0 = v 0 at hhead
    change Fin.tail u = Fin.tail v at htail
    rw [← Fin.cons_self_tail u, ← Fin.cons_self_tail v, hhead, htail]
  · intro av hav
    obtain ⟨ha,hv⟩ := mem_product.mp hav
    refine ⟨Fin.cons av.1 av.2, Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ha
      · exact Fintype.mem_piFinset.mp hv j
    · simp
  · intro u _
    rw [Fin.cons_self_tail]

theorem sum_piFinset_six (s : Fin 6 → Finset ℕ) (F : (Fin 6 → ℕ) → ℂ) :
    (∑ u ∈ Fintype.piFinset s, F u) =
      ∑ h ∈ s 0, ∑ k ∈ s 1, ∑ r ∈ s 2,
        ∑ t ∈ s 3, ∑ v ∈ s 4, ∑ p ∈ s 5, F ![h,k,r,t,v,p] := by
  simp only [sum_piFinset_succ]
  simp only [Fintype.piFinset_of_isEmpty, Fintype.sum_unique]
  apply sum_congr rfl
  intro h _
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro r _
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro v _
  apply sum_congr rfl
  intro p _
  congr 1

theorem weightedWattSum_eq_six_sums (positive : Bool) (p : WattScales)
    (a b : ℕ → ℂ) (u₀ u₁ : ℝ → ℂ) (γ : ℕ → ℕ → ℝ → ℝ → ℂ) :
    weightedWattSum positive p a b u₀ u₁ γ =
      ∑ h ∈ positiveRange p.H, ∑ k ∈ positiveRange p.C,
      ∑ r ∈ positiveRange p.R, ∑ s ∈ positiveRange p.S,
      ∑ v ∈ positiveRange p.V, ∑ t ∈ positiveRange p.P,
        if (r*v).Coprime (s*t) then
          u₀ h*u₁ k*a r*b s*γ r s v t*
            ePhase ((if positive then (1 : ℝ) else -1)*(h : ℝ)*k*
              (inverseRepresentative (r*v) (s*t) : ℝ)/(s*t : ℕ)) else 0 := by
  unfold weightedWattSum
  rw [sum_filter]
  unfold wattIndexSet
  rw [sum_piFinset_six]
  rfl

end
end Watt41
end DivisorProof
