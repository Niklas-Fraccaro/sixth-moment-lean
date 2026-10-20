import Mathlib.MeasureTheory.Integral.Prod
import SixthMoment.Denominator.Balanced.CoordinateMeasure
import SixthMoment.Denominator.Balanced.Halves
import SixthMoment.Denominator.Balanced.MomentDefinitions


namespace SixthMoment
open MeasureTheory Set
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

abbrev D02NestedSliceSpace := (Fin 4 → ℝ) × ((Fin 4 → ℝ) × ℝ)

def d02SliceFubiniIndex : (Fin 4 ⊕ (Fin 4 ⊕ Unit)) → Fin 5 ⊕ Fin 4 :=
  Sum.elim (fun i => .inl i.succ)
    (Sum.elim (fun i => .inr i) (fun _ => .inl 0))

def d02SliceFubiniIndexEquiv : (Fin 4 ⊕ (Fin 4 ⊕ Unit)) ≃ (Fin 5 ⊕ Fin 4) :=
  Equiv.ofBijective d02SliceFubiniIndex (by decide)

def d02SliceFubiniReindex : D02SliceCoordinateSpace ≃ᵐ (Fin 4 ⊕ (Fin 4 ⊕ Unit) → ℝ) :=
  MeasurableEquiv.arrowCongr' d02SliceFubiniIndexEquiv.symm (MeasurableEquiv.refl ℝ)

def d02SliceFubiniInner : (Fin 4 ⊕ Unit → ℝ) ≃ᵐ ((Fin 4 → ℝ) × ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 4 ⊕ Unit => ℝ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin 4 → ℝ))
      (MeasurableEquiv.funUnique Unit ℝ))

def d02SliceFubiniSplit : (Fin 4 ⊕ (Fin 4 ⊕ Unit) → ℝ) ≃ᵐ D02NestedSliceSpace :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 4 ⊕ (Fin 4 ⊕ Unit) => ℝ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin 4 → ℝ)) d02SliceFubiniInner)

def d02SliceFubiniEquiv : D02SliceCoordinateSpace ≃ᵐ D02NestedSliceSpace :=
  d02SliceFubiniReindex.trans d02SliceFubiniSplit

theorem d02SliceFubiniEquiv_measurePreserving :
    MeasurePreserving d02SliceFubiniEquiv volume volume := by
  have h₀ := volume_preserving_arrowCongr' d02SliceFubiniIndexEquiv.symm
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _)
  have h₁ := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 4 ⊕ Unit => ℝ)
  have h₂ := volume_preserving_funUnique Unit ℝ
  have h₃ := ((MeasurePreserving.id (volume : Measure (Fin 4 → ℝ))).prod h₂).comp h₁
  have h₄ := volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin 4 ⊕ (Fin 4 ⊕ Unit) => ℝ)
  have h₅ := ((MeasurePreserving.id (volume : Measure (Fin 4 → ℝ))).prod h₃).comp h₄
  exact h₅.comp h₀

theorem d02SliceFubiniEquiv_apply (a R : Fin 4 → ℝ) (u : ℝ) :
    d02SliceFubiniEquiv (Sum.elim ![u,a 0,a 1,a 2,a 3] R) = (a,(R,u)) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl

theorem d02SliceFubiniEquiv_symm_apply (z : D02NestedSliceSpace) :
    d02SliceFubiniEquiv.symm z = Sum.elim ![z.2.2,z.1 0,z.1 1,z.1 2,z.1 3] z.2.1 := by
  apply d02SliceFubiniEquiv.injective
  rw [d02SliceFubiniEquiv.apply_symm_apply,d02SliceFubiniEquiv_apply]

theorem d02SliceReconstruct_fubini (z : D02NestedSliceSpace) :
    d02SliceReconstruct (d02SliceFubiniEquiv.symm z) =
      d02BalancedEdges (z.1 0) (z.1 1) (z.1 2) (z.1 3) z.2.1 z.2.2 := by
  rw [d02SliceFubiniEquiv_symm_apply]
  rfl

theorem d02Edge_integral_fubini (f : D01EdgeSpace → ℝ) (hf : Integrable f) :
    (∫ x : D01EdgeSpace, f x) =
      ∫ a : Fin 4 → ℝ, ∫ R : Fin 4 → ℝ, ∫ u : ℝ,
        f (d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u) := by
  have hq : Integrable (fun q => f (d02SliceReconstruct q)) := by
    apply (d02SliceCoordinateChange_measurePreserving.integrable_comp_emb
      d02SliceCoordinateHomeomorph.measurableEmbedding).1
    change Integrable (fun x : D01EdgeSpace =>
      f (d02SliceReconstruct (d02SliceCoordinateChange x))) volume
    simpa only [d02SliceReconstruct_change] using hf
  have hz : Integrable (fun z : D02NestedSliceSpace =>
      f (d02SliceReconstruct (d02SliceFubiniEquiv.symm z))) :=
    (d02SliceFubiniEquiv_measurePreserving.symm.integrable_comp_emb
      d02SliceFubiniEquiv.symm.measurableEmbedding).2 hq
  calc
    _ = ∫ q, f (d02SliceReconstruct q) := d02SliceReconstruct_integral f
    _ = ∫ z : D02NestedSliceSpace,
        f (d02SliceReconstruct (d02SliceFubiniEquiv.symm z)) :=
      (d02SliceFubiniEquiv_measurePreserving.symm.integral_comp
        d02SliceFubiniEquiv.symm.measurableEmbedding _).symm
    _ = ∫ a : Fin 4 → ℝ, ∫ z : (Fin 4 → ℝ) × ℝ,
        f (d02SliceReconstruct (d02SliceFubiniEquiv.symm (a,z))) := integral_prod _ hz
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hz.prod_right_ae] with a ha
      rw [Measure.volume_eq_prod, integral_prod _ ha]
      simp_rw [d02SliceReconstruct_fubini]

def d02BalancedProfileCoordinates (x : D01EdgeSpace) : Fin 4 → ℝ :=
  ![(d01RowColumnSums x).1 1,(d01RowColumnSums x).1 2,
    (d01RowColumnSums x).2 1,(d01RowColumnSums x).2 2]

def d02BalancedEdgeProfile (ρ : Fin 4 → ℝ → ℝ) (x : D01EdgeSpace) : ℝ :=
  ∏ i, ρ i (d02BalancedProfileCoordinates x i)

def d02BalancedEdgePolynomial (p q : Fin 5 → ℝ) (x : D01EdgeSpace) : ℝ :=
  evalDegreeFour p (1/2-(d01RowColumnSums x).1 0) *
      evalDegreeFour q (1/2-(d01RowColumnSums x).2 0) +
    evalDegreeFour p ((d01RowColumnSums x).2 0-1/2) *
      evalDegreeFour q ((d01RowColumnSums x).1 0-1/2)

def d02BalancedEdgeCut : Set D01EdgeSpace :=
  {x | x∈d01NonnegativeOrthant ∧ d02ZetaLogSum (d01RowColumnSums x)≤1}

def d02BalancedEdgeIntegrand (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ) : D01EdgeSpace → ℝ :=
  d02BalancedEdgeCut.indicator (fun x =>
    d02BalancedEdgeProfile ρ x*d02BalancedEdgePolynomial p q x)

theorem d02BalancedEdgeCut_closed : IsClosed d02BalancedEdgeCut := by
  unfold d02BalancedEdgeCut d01NonnegativeOrthant
  have horth : IsClosed {x : D01EdgeSpace | ∀ ij, 0≤x ij} := by
    rw [show {x : D01EdgeSpace | ∀ ij, 0≤x ij} =
      ⋂ ij, {x : D01EdgeSpace | 0≤x ij} from by ext x; simp]
    exact isClosed_iInter fun ij => isClosed_le continuous_const (continuous_apply ij)
  have hcut : Continuous (fun x : D01EdgeSpace =>
      d02ZetaLogSum (d01RowColumnSums x)) := by
    unfold d02ZetaLogSum d01RowColumnSums
    fun_prop
  exact horth.inter (isClosed_le hcut continuous_const)

theorem d02BalancedEdgePolynomial_continuous (p q : Fin 5 → ℝ) :
    Continuous (d02BalancedEdgePolynomial p q) := by
  unfold d02BalancedEdgePolynomial evalDegreeFour d01RowColumnSums
  fun_prop

theorem d02BalancedEdgeProfile_continuous (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i, Continuous (ρ i)) : Continuous (d02BalancedEdgeProfile ρ) := by
  unfold d02BalancedEdgeProfile
  apply continuous_finsetProd
  intro i _
  apply (hρ i).comp
  fin_cases i <;> simp [d02BalancedProfileCoordinates,d01RowColumnSums] <;> fun_prop

theorem d02BalancedProfileCoordinates_edges (a b c d : ℝ) (R : Fin 4 → ℝ) (u : ℝ) :
    d02BalancedProfileCoordinates (d02BalancedEdges a b c d R u) = ![a,b,c,d] := by
  unfold d02BalancedProfileCoordinates
  rw [d02BalancedEdges_rowColumnSums]
  rfl

def d02BalancedEdgeBound (a : Fin 4 → ℝ) : ℝ := 1+∑ i, |a i|

theorem d02BalancedEdgeBound_one_le (a : Fin 4 → ℝ) : 1≤d02BalancedEdgeBound a := by
  unfold d02BalancedEdgeBound
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem d02BalancedEdgeBound_cap_le (a : Fin 4 → ℝ) (i : Fin 4) :
    a i≤d02BalancedEdgeBound a := by
  have h := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => abs_nonneg (a j))
    (Finset.mem_univ i)
  exact (le_abs_self _).trans (h.trans (by unfold d02BalancedEdgeBound; linarith))

theorem d02BalancedEdge_profile_nonzero_bounded (ρ : Fin 4 → ℝ → ℝ)
    (a : Fin 4 → ℝ) (hρ : ∀ i t, ρ i t≠0 → t∈Icc 0 (a i))
    {x : D01EdgeSpace} (hx : x∈d02BalancedEdgeCut)
    (hprod : d02BalancedEdgeProfile ρ x≠0) :
    x∈Icc (fun _ => (0:ℝ)) (fun _ => d02BalancedEdgeBound a) := by
  have hrows (i : Fin 4) : d02BalancedProfileCoordinates x i≤a i :=
    (hρ i _ ((Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i))).2
  have hr1 := hrows 0
  have hr2 := hrows 1
  have h00 := hx.1 (0,0)
  have h01 := hx.1 (0,1)
  have h02 := hx.1 (0,2)
  have h10 := hx.1 (1,0)
  have h11 := hx.1 (1,1)
  have h12 := hx.1 (1,2)
  have h20 := hx.1 (2,0)
  have h21 := hx.1 (2,1)
  have h22 := hx.1 (2,2)
  have hcut := hx.2
  have hB0 := d02BalancedEdgeBound_one_le a
  have hB1 := d02BalancedEdgeBound_cap_le a 0
  have hB2 := d02BalancedEdgeBound_cap_le a 1
  simp [d02BalancedProfileCoordinates,d01RowColumnSums,Fin.sum_univ_succ] at hr1 hr2
  simp [d02ZetaLogSum,d01RowColumnSums,Fin.sum_univ_succ] at hcut
  refine ⟨hx.1, ?_⟩
  rintro ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> dsimp <;> linarith

theorem d02BalancedEdge_nonzero_bounded (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (a : Fin 4 → ℝ) (hρ : ∀ i t, ρ i t≠0 → t∈Icc 0 (a i))
    {x : D01EdgeSpace} (hx : x∈d02BalancedEdgeCut)
    (hn : d02BalancedEdgeProfile ρ x*d02BalancedEdgePolynomial p q x≠0) :
    x∈Icc (fun _ => (0:ℝ)) (fun _ => d02BalancedEdgeBound a) :=
  d02BalancedEdge_profile_nonzero_bounded ρ a hρ hx (mul_ne_zero_iff.mp hn).1

theorem d02BalancedEdgeIntegrand_integrable (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ) (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (a i)) :
    Integrable (d02BalancedEdgeIntegrand p q ρ) := by
  let K := Icc (fun _ : Fin 3 × Fin 3 => (0:ℝ)) (fun _ => d02BalancedEdgeBound a)
  let E := d02BalancedEdgeCut∩K
  let g := fun x => d02BalancedEdgeProfile ρ x*d02BalancedEdgePolynomial p q x
  have hg : Continuous g := (d02BalancedEdgeProfile_continuous ρ hρc).mul
    (d02BalancedEdgePolynomial_continuous p q)
  have hE : IsCompact E := (isCompact_Icc : IsCompact K).inter_left d02BalancedEdgeCut_closed
  have hi := (hg.continuousOn.integrableOn_compact (μ := volume) hE).integrable_indicator
    hE.measurableSet
  convert hi using 1
  funext x
  change d02BalancedEdgeCut.indicator g x = E.indicator g x
  by_cases hx : x∈d02BalancedEdgeCut
  · rw [indicator_of_mem hx]
    by_cases hn : g x=0
    · simp [Set.indicator_apply,hn]
    · have hK : x∈K := d02BalancedEdge_nonzero_bounded p q ρ a hρcap hx hn
      rw [indicator_of_mem (show x∈E from ⟨hx,hK⟩)]
  · have hnot : x∉E := fun he => hx he.1
    rw [indicator_of_notMem hx,indicator_of_notMem hnot]

theorem d02BalancedEdgeProfile_edges (ρ : Fin 4 → ℝ → ℝ) (a R : Fin 4 → ℝ) (u : ℝ) :
    d02BalancedEdgeProfile ρ (d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u) =
      ∏ i, ρ i (a i) := by
  unfold d02BalancedEdgeProfile
  rw [d02BalancedProfileCoordinates_edges]
  apply Finset.prod_congr rfl
  intro i _
  fin_cases i <;> rfl

theorem d02BalancedEdgeIntegrand_edges (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (a R : Fin 4 → ℝ) (u : ℝ) :
    d02BalancedEdgeIntegrand p q ρ (d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u) =
      if R∈denominatorRegion (a 0) (a 1) (a 2) (a 3) then
        (Icc 0 (d02BalancedWidth (a 0) (a 1) (a 2) (a 3) R/2)).indicator
          (fun u => (∏ i, ρ i (a i)) *
            d02BalancedEdgePolynomial p q (d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u)) u
      else 0 := by
  have hc : d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u∈d02BalancedEdgeCut ↔
      R∈denominatorRegion (a 0) (a 1) (a 2) (a 3) ∧
        u∈Icc 0 (d02BalancedWidth (a 0) (a 1) (a 2) (a 3) R/2) :=
    d02BalancedEdges_slice_iff (a 0) (a 1) (a 2) (a 3) R u
  unfold d02BalancedEdgeIntegrand
  simp only [Set.indicator_apply]
  rw [hc,d02BalancedEdgeProfile_edges]
  by_cases hR : R∈denominatorRegion (a 0) (a 1) (a 2) (a 3)
  · simp [hR]
  · simp [hR]

theorem d02BalancedProfileSum_eq_sum (a : Fin 4 → ℝ) :
    d02ProfileSum (a 0) (a 1) (a 2) (a 3) = ∑ i, a i := by
  simp only [d02ProfileSum,Fin.sum_univ_succ,Fin.sum_univ_zero]
  change a 0+a 1+a 2+a 3 = a 0+(a 1+(a 2+(a 3+0)))
  ring

theorem d02BalancedProfileSum_lt_one (ρ : Fin 4 → ℝ → ℝ) (A a : Fin 4 → ℝ)
    (hA : (∑ i, A i)<1) (hρ : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i))
    (hp : (∏ i, ρ i (a i))≠0) :
    d02ProfileSum (a 0) (a 1) (a 2) (a 3)<1 := by
  rw [d02BalancedProfileSum_eq_sum]
  apply lt_of_le_of_lt _ hA
  apply Finset.sum_le_sum
  intro i _
  exact (hρ i _ ((Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ i))).2

theorem d02BalancedEdgePolynomial_slice_integral (p q : Fin 5 → ℝ)
    (a R : Fin 4 → ℝ) :
    (∫ u in (0:ℝ)..(d02BalancedWidth (a 0) (a 1) (a 2) (a 3) R/2),
      d02BalancedEdgePolynomial p q (d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u)) =
      denominatorRealInner p q (d02ProfileDelta (a 0) (a 1) (a 2) (a 3))
        (d02BalancedWidth (a 0) (a 1) (a 2) (a 3) R/2) := by
  have h₁ : Continuous (fun u : ℝ =>
      evalDegreeFour p (1/2-(d01RowColumnSums
        (d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u)).1 0) *
      evalDegreeFour q (1/2-(d01RowColumnSums
        (d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u)).2 0)) := by
    unfold evalDegreeFour d01RowColumnSums d02BalancedEdges
    fun_prop
  have h₂ : Continuous (fun u : ℝ =>
      evalDegreeFour p ((d01RowColumnSums
        (d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u)).2 0-1/2) *
      evalDegreeFour q ((d01RowColumnSums
        (d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u)).1 0-1/2)) := by
    unfold evalDegreeFour d01RowColumnSums d02BalancedEdges
    fun_prop
  unfold d02BalancedEdgePolynomial
  rw [intervalIntegral.integral_add (h₁.intervalIntegrable _ _) (h₂.intervalIntegrable _ _)]
  exact d02BalancedSlices_eq_inner p q (a 0) (a 1) (a 2) (a 3) R

theorem d02BalancedEdgeIntegrand_free_edge_integral (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (A a R : Fin 4 → ℝ)
    (hA : (∑ i, A i)<1) (hρ : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    (∫ u : ℝ, d02BalancedEdgeIntegrand p q ρ
      (d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u)) =
      (denominatorRegion (a 0) (a 1) (a 2) (a 3)).indicator
        (fun R => (∏ i, ρ i (a i)) * denominatorRealInner p q
          (d02ProfileDelta (a 0) (a 1) (a 2) (a 3))
          (d02BalancedWidth (a 0) (a 1) (a 2) (a 3) R/2)) R := by
  simp_rw [d02BalancedEdgeIntegrand_edges]
  by_cases hR : R∈denominatorRegion (a 0) (a 1) (a 2) (a 3)
  · simp only [hR,ite_true,indicator_of_mem hR]
    by_cases hp : (∏ i, ρ i (a i))=0
    · simp [hp]
    · have hwidth : 0<d02BalancedWidth (a 0) (a 1) (a 2) (a 3) R :=
        d02BalancedWidth_pos (d02BalancedProfileSum_lt_one ρ A a hA hρ hp) hR
      rw [indicator_Icc_integral _ _ _ (by positivity :
        0≤d02BalancedWidth (a 0) (a 1) (a 2) (a 3) R/2),
        intervalIntegral.integral_const_mul,d02BalancedEdgePolynomial_slice_integral]
  · simp [hR]

theorem d02BalancedEdgeIntegrand_interior_integral (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (A a : Fin 4 → ℝ)
    (hA : (∑ i, A i)<1) (hρ : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    (∫ R : Fin 4 → ℝ, ∫ u : ℝ, d02BalancedEdgeIntegrand p q ρ
      (d02BalancedEdges (a 0) (a 1) (a 2) (a 3) R u)) =
      (∏ i, ρ i (a i))*denominatorZeroKernel p q (a 0) (a 1) (a 2) (a 3) := by
  simp_rw [d02BalancedEdgeIntegrand_free_edge_integral p q ρ A a _ hA hρ]
  rw [integral_indicator (denominatorRegion_closed _ _ _ _).measurableSet,
    integral_const_mul]
  congr 1
  simp_rw [← d02BalancedHalves_eq_inner]
  exact d02BalancedHalves_eq_kernel p q (a 0) (a 1) (a 2) (a 3)

theorem d02BalancedEdgeIntegral_eq_profileKernel (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hA : (∑ i, A i)<1) (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    (∫ x : D01EdgeSpace, d02BalancedEdgeIntegrand p q ρ x) =
      d02BalancedProfileKernel p q ρ := by
  rw [d02Edge_integral_fubini _ (d02BalancedEdgeIntegrand_integrable p q ρ A hρc hρcap)]
  simp_rw [d02BalancedEdgeIntegrand_interior_integral p q ρ A _ hA hρcap]
  rfl

end
end SixthMoment
