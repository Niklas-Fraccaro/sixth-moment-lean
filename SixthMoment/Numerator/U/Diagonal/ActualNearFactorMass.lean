import SixthMoment.Numerator.U.Diagonal.NearFactorMass
import SixthMoment.Numerator.U.Reconstruction.RectangularNearUnitExclusion


namespace SixthMoment
open Source
open scoped BigOperators
open Classical
noncomputable section

def bblrAFEFactorPairs (n : Fin 4 → ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((n 0+1,n 1+1),(n 2+1,n 3+1))

theorem bblrAFEFactorPairs_injective : Function.Injective bblrAFEFactorPairs := by
  intro n m h
  have h0 := congrArg (fun pq => pq.1.1) h
  have h1 := congrArg (fun pq => pq.1.2) h
  have h2 := congrArg (fun pq => pq.2.1) h
  have h3 := congrArg (fun pq => pq.2.2) h
  simp only [bblrAFEFactorPairs,Nat.add_right_cancel_iff] at h0 h1 h2 h3
  funext j
  fin_cases j <;> assumption

theorem bblrAFEFactorPairs_mem_nearBlock {L P J Q u v h H : ℕ}
    (positive : Bool) (n : Fin 4 → ℕ)
    (hMlo : L≤(n 0+1)*(n 1+1)) (hMhi : (n 0+1)*(n 1+1)≤P)
    (hNlo : J≤(n 2+1)*(n 3+1)) (hNhi : (n 2+1)*(n 3+1)≤Q)
    (hrel : signedQuadraticRelation positive (rectangularAFESourceTuple u v n h))
    (hh : h≤H) :
    bblrAFEFactorPairs n ∈ positiveNearFactorBlock L P J Q u v H := by
  have hgap := rectangular_signed_relation_abs_gap positive
    (rectangularAFESourceTuple u v n h) hrel
  have hgaple : |((u*(n 0+1)*(n 1+1) : ℕ):ℝ)-
      ((v*(n 2+1)*(n 3+1) : ℕ):ℝ)|≤(H:ℝ) := by
    have hhreal : (h:ℝ)≤H := by exact_mod_cast hh
    simpa [rectangularNearLeftProduct,rectangularNearRightProduct,
      rectangularAFESourceTuple] using hgap.le.trans hhreal
  have hnear1 : u*((n 0+1)*(n 1+1))≤v*((n 2+1)*(n 3+1))+H := by
    have hr := (le_abs_self _).trans hgaple
    have he : ((u*(n 0+1)*(n 1+1) : ℕ):ℝ)≤
        ((v*(n 2+1)*(n 3+1) : ℕ):ℝ)+H := by linarith
    have hn : u*(n 0+1)*(n 1+1)≤v*(n 2+1)*(n 3+1)+H := by exact_mod_cast he
    simpa [Nat.mul_assoc] using hn
  have hnear2 : v*((n 2+1)*(n 3+1))≤u*((n 0+1)*(n 1+1))+H := by
    have hr := (neg_le_abs _).trans hgaple
    have he : ((v*(n 2+1)*(n 3+1) : ℕ):ℝ)≤
        ((u*(n 0+1)*(n 1+1) : ℕ):ℝ)+H := by linarith
    have hn : v*(n 2+1)*(n 3+1)≤u*(n 0+1)*(n 1+1)+H := by exact_mod_cast he
    simpa [Nat.mul_assoc] using hn
  apply Finset.mem_filter.mpr
  refine ⟨mem_positiveNearFactorRectangle.mpr ⟨?_,?_⟩,hMlo,hNlo⟩
  · exact mem_positiveProductFactorPairs.mpr ⟨by omega,by omega,hMhi⟩
  · exact Finset.mem_filter.mpr
      ⟨mem_positiveProductFactorPairs.mpr ⟨by omega,by omega,hNhi⟩,hnear1,hnear2⟩

theorem bblrActualNearAFE_mass_le_harmonic {L P J Q u v H K : ℕ}
    (hu : 0<u) (hv : 0<v) (hL : 0<L) (hJ : 0<J) (hQ : Q≤K^2)
    (s : Finset (Fin 4 → ℕ))
    (hs : ∀ n∈s, bblrAFEFactorPairs n ∈ positiveNearFactorBlock L P J Q u v H) :
    (∑ n∈s,positiveNearFactorWeight u v (bblrAFEFactorPairs n))≤
      (P:ℝ)*(harmonic P : ℝ)*
        (2*(2*(H:ℝ)/(v:ℝ)+1)*(harmonic K : ℝ)+2*K)/
          Real.sqrt ((u:ℝ)*v*L*J) := by
  have hsub : s.image bblrAFEFactorPairs ⊆ positiveNearFactorBlock L P J Q u v H := by
    intro pq hpq
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hpq
    exact hs n hn
  calc
    _ = ∑ pq∈s.image bblrAFEFactorPairs,positiveNearFactorWeight u v pq := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => bblrAFEFactorPairs_injective h
    _ ≤ ∑ pq∈positiveNearFactorBlock L P J Q u v H,
        positiveNearFactorWeight u v pq :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun pq _ _ => positiveNearFactorWeight_nonneg u v pq)
    _ ≤ _ := positiveNearFactorBlock_mass_le_harmonic hu hv hL hJ hQ

end
end SixthMoment
