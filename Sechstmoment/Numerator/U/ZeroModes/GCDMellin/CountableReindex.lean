import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.CountableJoint

/-! Reindexing the actual Dirichlet zero-index convention by the three
positive natural indices used by the unrestricted native expression. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

def a03GCDNaturalSuccessor (k : (ℕ×ℕ)×ℕ) : (ℕ×ℕ)×ℕ :=
  ((k.1.1+1,k.1.2+1),k.2+1)

theorem a03GCDNaturalSuccessor_injective : Function.Injective a03GCDNaturalSuccessor := by
  intro k l hEq
  rcases k with ⟨⟨m,n⟩,h⟩
  rcases l with ⟨⟨M,N⟩,H⟩
  simpa only [a03GCDNaturalSuccessor,Prod.mk.injEq,Nat.add_left_inj] using hEq

theorem a03GCDNaturalSuccessor_tsum (F : (ℕ×ℕ)×ℕ→ℂ)
    (hm : ∀ n h : ℕ,F ((0,n),h)=0)
    (hn : ∀ m h : ℕ,F ((m,0),h)=0)
    (hh : ∀ m n : ℕ,F ((m,n),0)=0) :
    (∑' k : (ℕ×ℕ)×ℕ,F (a03GCDNaturalSuccessor k))=∑' k : (ℕ×ℕ)×ℕ,F k := by
  apply a03GCDNaturalSuccessor_injective.tsum_eq
  intro k hk
  change F k≠0 at hk
  have hm0 : k.1.1≠0 := by
    intro he
    apply hk
    simpa only [←he] using hm k.1.2 k.2
  have hn0 : k.1.2≠0 := by
    intro he
    apply hk
    simpa only [←he] using hn k.1.1 k.2
  have hh0 : k.2≠0 := by
    intro he
    apply hk
    simpa only [←he] using hh k.1.1 k.1.2
  refine ⟨((k.1.1-1,k.1.2-1),k.2-1),?_⟩
  simp only [a03GCDNaturalSuccessor,
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0),
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn0),
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hh0)]

theorem a03ZeroModeGCDInitialMNHKernel_shifted_integral_tsum
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ) :
    (∑' k : (ℕ×ℕ)×ℕ,∫ p : A03GCDMellinCoordinates,
      a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B p.1
        (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p)
          ((k.1.1+1,k.1.2+1),k.2+1) ∂a03GCDMellinMeasure)=
      ∫ p : A03GCDMellinCoordinates,a03ZeroModeGCDInitialKernel Φ T σ α a b A B p.1
        (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p) ∂a03GCDMellinMeasure := by
  let F : (ℕ×ℕ)×ℕ→ℂ := fun k => ∫p : A03GCDMellinCoordinates,
    a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B p.1
      (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p) k ∂a03GCDMellinMeasure
  change (∑' k : (ℕ×ℕ)×ℕ,F (a03GCDNaturalSuccessor k))=_
  rw [a03GCDNaturalSuccessor_tsum F]
  · exact a03ZeroModeGCDInitialMNHKernel_integral_tsum hΦ hSupp hT hε hε1 σ α hα ha hb A B
  all_goals
    intros
    simp [F,a03ZeroModeGCDInitialMNHKernel,a03GCDDirichletTerm]

end
end Sechstmoment.Source
