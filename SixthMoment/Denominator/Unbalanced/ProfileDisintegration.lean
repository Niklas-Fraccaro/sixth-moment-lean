import Mathlib.MeasureTheory.Integral.Prod
import SixthMoment.Certificate.Kernels.Balanced.RegionIntegral
import SixthMoment.Denominator.Unbalanced.CoordinateMeasure
import SixthMoment.Denominator.Unbalanced.MomentDefinitions

namespace SixthMoment
open MeasureTheory Set
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 0

abbrev D04SplitRealSpace := ℝ × (ℝ × ℝ)
abbrev D04NestedSliceSpace := (Fin 4 → ℝ) × ((Fin 2 → ℝ) × D04SplitRealSpace)
abbrev D04FubiniIndex := Fin 4 ⊕ (Fin 2 ⊕ (Unit ⊕ (Unit ⊕ Unit)))

def d04SliceFubiniIndex : D04FubiniIndex → Fin 4 ⊕ Fin 5 :=
  Sum.elim Sum.inl (Sum.elim (fun i => .inr i.castSucc.castSucc.castSucc)
    (Sum.elim (fun _ => .inr 2) (Sum.elim (fun _ => .inr 3) (fun _ => .inr 4))))
def d04SliceFubiniIndexEquiv : D04FubiniIndex ≃ (Fin 4 ⊕ Fin 5) :=
  Equiv.ofBijective d04SliceFubiniIndex (by decide)
def d04SliceFubiniReindex : D04SliceCoordinateSpace ≃ᵐ (D04FubiniIndex → ℝ) :=
  MeasurableEquiv.arrowCongr' d04SliceFubiniIndexEquiv.symm (MeasurableEquiv.refl ℝ)

def d04SliceFubiniLast : (Unit ⊕ Unit → ℝ) ≃ᵐ (ℝ × ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ Unit => ℝ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit ℝ)
      (MeasurableEquiv.funUnique Unit ℝ))
def d04SliceFubiniTriple : (Unit ⊕ (Unit ⊕ Unit) → ℝ) ≃ᵐ D04SplitRealSpace :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ (Unit ⊕ Unit) => ℝ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit ℝ) d04SliceFubiniLast)
def d04SliceFubiniInner : (Fin 2 ⊕ (Unit ⊕ (Unit ⊕ Unit)) → ℝ) ≃ᵐ
    ((Fin 2 → ℝ) × D04SplitRealSpace) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin 2 ⊕ (Unit ⊕ (Unit ⊕ Unit)) => ℝ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin 2 → ℝ)) d04SliceFubiniTriple)
def d04SliceFubiniSplit : (D04FubiniIndex → ℝ) ≃ᵐ D04NestedSliceSpace :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : D04FubiniIndex => ℝ)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl (Fin 4 → ℝ)) d04SliceFubiniInner)
def d04SliceFubiniEquiv : D04SliceCoordinateSpace ≃ᵐ D04NestedSliceSpace :=
  d04SliceFubiniReindex.trans d04SliceFubiniSplit

theorem d04SliceFubiniEquiv_measurePreserving :
    MeasurePreserving d04SliceFubiniEquiv volume volume := by
  have hU := volume_preserving_funUnique Unit ℝ
  have h₂ := (hU.prod hU).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Unit ⊕ Unit => ℝ))
  have h₃ := (hU.prod h₂).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : Unit ⊕ (Unit ⊕ Unit) => ℝ))
  have h₄ := ((MeasurePreserving.id (volume : Measure (Fin 2 → ℝ))).prod h₃).comp
    (volume_measurePreserving_sumPiEquivProdPi
      (fun _ : Fin 2 ⊕ (Unit ⊕ (Unit ⊕ Unit)) => ℝ))
  have h₅ := ((MeasurePreserving.id (volume : Measure (Fin 4 → ℝ))).prod h₄).comp
    (volume_measurePreserving_sumPiEquivProdPi (fun _ : D04FubiniIndex => ℝ))
  exact h₅.comp (volume_preserving_arrowCongr' d04SliceFubiniIndexEquiv.symm
    (MeasurableEquiv.refl ℝ) (MeasurePreserving.id _))

theorem d04SliceFubiniEquiv_apply (a : Fin 4 → ℝ) (u : Fin 2 → ℝ) (y z t : ℝ) :
    d04SliceFubiniEquiv (Sum.elim a ![u 0,u 1,y,z,t]) = (a,(u,(y,z,t))) := by
  apply Prod.ext
  · funext i
    fin_cases i <;> rfl
  · apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl

theorem d04SliceFubiniEquiv_symm_apply (z : D04NestedSliceSpace) :
    d04SliceFubiniEquiv.symm z =
      Sum.elim z.1 ![z.2.1 0,z.2.1 1,z.2.2.1,z.2.2.2.1,z.2.2.2.2] := by
  apply d04SliceFubiniEquiv.injective
  rw [d04SliceFubiniEquiv.apply_symm_apply,d04SliceFubiniEquiv_apply]

theorem d04SliceReconstruct_fubini (z : D04NestedSliceSpace) :
    d04SliceReconstruct (d04SliceFubiniEquiv.symm z) =
      d04UnbalancedEdges (z.1 0) (z.1 1) (z.1 2) (z.1 3) z.2.1
        ![z.2.2.1,z.2.2.2.1,z.2.2.2.2] := by
  rw [d04SliceFubiniEquiv_symm_apply]
  rfl

theorem d04Edge_integral_fubini {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : D01EdgeSpace → E) (hf : Integrable f) :
    (∫ x : D01EdgeSpace, f x) =
      ∫ a : Fin 4 → ℝ, ∫ u : Fin 2 → ℝ, ∫ y : ℝ, ∫ z : ℝ, ∫ t : ℝ,
        f (d04UnbalancedEdges (a 0) (a 1) (a 2) (a 3) u ![y,z,t]) := by
  have hq : Integrable (fun q => f (d04SliceReconstruct q)) := by
    apply (d04SliceCoordinateChange_measurePreserving.integrable_comp_emb
      d04SliceCoordinateHomeomorph.measurableEmbedding).1
    change Integrable (fun x : D01EdgeSpace =>
      f (d04SliceReconstruct (d04SliceCoordinateChange x))) volume
    simpa only [d04SliceReconstruct_change] using hf
  have hz : Integrable (fun z : D04NestedSliceSpace =>
      f (d04SliceReconstruct (d04SliceFubiniEquiv.symm z))) :=
    (d04SliceFubiniEquiv_measurePreserving.symm.integrable_comp_emb
      d04SliceFubiniEquiv.symm.measurableEmbedding).2 hq
  calc
    _ = ∫ q, f (d04SliceReconstruct q) := d04SliceReconstruct_integral f
    _ = ∫ z : D04NestedSliceSpace,
        f (d04SliceReconstruct (d04SliceFubiniEquiv.symm z)) :=
      (d04SliceFubiniEquiv_measurePreserving.symm.integral_comp
        d04SliceFubiniEquiv.symm.measurableEmbedding _).symm
    _ = ∫ a : Fin 4 → ℝ, ∫ z : (Fin 2 → ℝ) × D04SplitRealSpace,
        f (d04SliceReconstruct (d04SliceFubiniEquiv.symm (a,z))) := integral_prod _ hz
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hz.prod_right_ae] with a ha
      rw [Measure.volume_eq_prod,integral_prod _ ha]
      apply integral_congr_ae
      filter_upwards [ha.prod_right_ae] with u hu
      rw [Measure.volume_eq_prod,integral_prod _ hu]
      apply integral_congr_ae
      filter_upwards [hu.prod_right_ae] with y hy
      rw [Measure.volume_eq_prod,integral_prod _ hy]
      simp_rw [d04SliceReconstruct_fubini]

theorem d04UnbalancedEdgeProfile_eq_prod (ρ : Fin 4 → ℝ → ℝ) (x : D01EdgeSpace) :
    d04UnbalancedEdgeProfile ρ x = ∏ i, ρ i (d04UnbalancedProfileCoordinates x i) := by
  simp [d04UnbalancedEdgeProfile,d04UnbalancedProfileCoordinates,Fin.prod_univ_succ]
  ring
def d04UnbalancedEdgePolynomial (p q : Fin 5 → ℝ) (x : D01EdgeSpace) : ℝ :=
  evalDegreeFour p ((d01RowColumnSums x).2 0-1/2) *
    evalDegreeFour q (1/2-(d01RowColumnSums x).2 1)
def d04UnbalancedEdgeIntegrand (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ) :
    D01EdgeSpace → ℝ :=
  d01NonnegativeOrthant.indicator (fun x =>
    d04UnbalancedEdgeProfile ρ x*d04UnbalancedEdgePolynomial p q x)
def d04UnbalancedEdgeBound (A : Fin 4 → ℝ) : ℝ := 1+∑ i, |A i|

theorem d04UnbalancedOrthant_closed : IsClosed d01NonnegativeOrthant := by
  unfold d01NonnegativeOrthant
  rw [show {x : D01EdgeSpace | ∀ ij, 0≤x ij} =
    ⋂ ij, {x : D01EdgeSpace | 0≤x ij} from by ext x; simp]
  exact isClosed_iInter fun ij => isClosed_le continuous_const (continuous_apply ij)

theorem d04UnbalancedEdgeProfile_continuous (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i, Continuous (ρ i)) : Continuous (d04UnbalancedEdgeProfile ρ) := by
  rw [show d04UnbalancedEdgeProfile ρ = (fun x => ∏ i, ρ i (d04UnbalancedProfileCoordinates x i))
    from funext (d04UnbalancedEdgeProfile_eq_prod ρ)]
  apply continuous_finsetProd
  intro i _
  apply (hρ i).comp
  fin_cases i <;> simp [d04UnbalancedProfileCoordinates,d01RowColumnSums] <;> fun_prop

theorem d04UnbalancedEdgePolynomial_continuous (p q : Fin 5 → ℝ) :
    Continuous (d04UnbalancedEdgePolynomial p q) := by
  unfold d04UnbalancedEdgePolynomial evalDegreeFour d01RowColumnSums
  fun_prop

theorem d04UnbalancedEdgeBound_cap_le (A : Fin 4 → ℝ) (i : Fin 4) :
    A i≤d04UnbalancedEdgeBound A := by
  have h := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => abs_nonneg (A j))
    (Finset.mem_univ i)
  exact (le_abs_self _).trans (h.trans (by unfold d04UnbalancedEdgeBound; linarith))

theorem d04UnbalancedEdge_profile_nonzero_bounded (ρ : Fin 4 → ℝ → ℝ)
    (A : Fin 4 → ℝ) (hρ : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i))
    {x : D01EdgeSpace} (hx : x∈d01NonnegativeOrthant)
    (hprod : d04UnbalancedEdgeProfile ρ x≠0) :
    x∈Icc (fun _ => (0:ℝ)) (fun _ => d04UnbalancedEdgeBound A) := by
  rw [d04UnbalancedEdgeProfile_eq_prod] at hprod
  have hrows (i : Fin 4) : d04UnbalancedProfileCoordinates x i≤A i :=
    (hρ i _ ((Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i))).2
  refine ⟨hx, ?_⟩
  rintro ⟨i,j⟩
  have hrow : (d01RowColumnSums x).1 i≤d04UnbalancedEdgeBound A := by
    fin_cases i
    · exact (hrows 0).trans (d04UnbalancedEdgeBound_cap_le A 0)
    · exact (hrows 1).trans (d04UnbalancedEdgeBound_cap_le A 1)
    · exact (hrows 2).trans (d04UnbalancedEdgeBound_cap_le A 2)
  exact (Finset.single_le_sum (fun k (_ : k∈Finset.univ) => hx (i,k))
    (Finset.mem_univ j)).trans hrow

theorem d04UnbalancedEdgeIntegrand_integrable (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    Integrable (d04UnbalancedEdgeIntegrand p q ρ) := by
  let K := Icc (fun _ : Fin 3 × Fin 3 => (0:ℝ)) (fun _ => d04UnbalancedEdgeBound A)
  let E := d01NonnegativeOrthant∩K
  let g := fun x => d04UnbalancedEdgeProfile ρ x*d04UnbalancedEdgePolynomial p q x
  have hg : Continuous g := (d04UnbalancedEdgeProfile_continuous ρ hρc).mul
    (d04UnbalancedEdgePolynomial_continuous p q)
  have hE : IsCompact E := (isCompact_Icc : IsCompact K).inter_left d04UnbalancedOrthant_closed
  have hi := (hg.continuousOn.integrableOn_compact (μ := volume) hE).integrable_indicator
    hE.measurableSet
  convert hi using 1
  funext x
  change d01NonnegativeOrthant.indicator g x = E.indicator g x
  by_cases hx : x∈d01NonnegativeOrthant
  · rw [indicator_of_mem hx]
    by_cases hn : g x=0
    · simp [Set.indicator_apply,hn]
    · have hp : d04UnbalancedEdgeProfile ρ x≠0 := (mul_ne_zero_iff.mp hn).1
      have hK : x∈K := d04UnbalancedEdge_profile_nonzero_bounded ρ A hρcap hx hp
      rw [indicator_of_mem (show x∈E from ⟨hx,hK⟩)]
  · rw [indicator_of_notMem hx,indicator_of_notMem (show x∉E from fun he => hx he.1)]


theorem d04UnbalancedEdgeProfile_edges (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (u : Fin 2 → ℝ) (y : Fin 3 → ℝ) :
    d04UnbalancedEdgeProfile ρ (d04UnbalancedEdges (a 0) (a 1) (a 2) (a 3) u y) =
      ∏ i, ρ i (a i) := by
  simp_rw [d04UnbalancedEdgeProfile_eq_prod]
  rw [d04UnbalancedProfileCoordinates_edges]
  apply Finset.prod_congr rfl
  intro i _
  fin_cases i <;> rfl

theorem d04UnbalancedEdgePolynomial_centered (p q : Fin 5 → ℝ)
    (a b c d : ℝ) (u : Fin 2 → ℝ) (y z t : ℝ) :
    d04UnbalancedEdgePolynomial p q (d04UnbalancedEdges a b c d u ![y,z,t]) =
      evalDegreeFour p ((y-(a-u 0)/2)+(z-(b-u 1)/2)+
        (t-(c-(d-u 0-u 1))/2)-minusKernelT0 a b c d)*
      evalDegreeFour q ((y-(a-u 0)/2)+(z-(b-u 1)/2)+
        (t-(c-(d-u 0-u 1))/2)+minusKernelT0 a b c d) := by
  have h := d04UnbalancedEdges_centered_arguments a b c d u ![y,z,t]
  unfold d04UnbalancedEdgePolynomial
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  dsimp only at h₁ h₂
  rw [h₁,h₂]
  have hc : d04UnbalancedCenteredSplit a b c d u ![y,z,t] =
      (y-(a-u 0)/2)+(z-(b-u 1)/2)+(t-(c-(d-u 0-u 1))/2) := by
    simp [d04UnbalancedCenteredSplit,minusKernelH]
    ring
  rw [hc]

theorem d04TripleInterval_translate (r s t : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    (∫ x in (0:ℝ)..r, ∫ y in (0:ℝ)..s, ∫ z in (0:ℝ)..t,
      f (x-r/2) (y-s/2) (z-t/2)) = boxIntegral r s t f := by
  have h₃ (x y : ℝ) :
      (∫ z in (0:ℝ)..t, f (x-r/2) (y-s/2) (z-t/2)) =
        ∫ z in -(t/2)..t/2, f (x-r/2) (y-s/2) z := by
    simpa only [zero_sub,show t-t/2=t/2 by ring] using
      intervalIntegral.integral_comp_sub_right (fun z => f (x-r/2) (y-s/2) z) (a := (0:ℝ)) (b := t) (t/2)
  simp_rw [h₃]
  have h₂ (x : ℝ) :
      (∫ y in (0:ℝ)..s, ∫ z in -(t/2)..t/2, f (x-r/2) (y-s/2) z) =
        ∫ y in -(s/2)..s/2, ∫ z in -(t/2)..t/2, f (x-r/2) y z := by
    simpa only [zero_sub,show s-s/2=s/2 by ring] using
      intervalIntegral.integral_comp_sub_right
        (fun y => ∫ z in -(t/2)..t/2, f (x-r/2) y z) (a := (0:ℝ)) (b := s) (s/2)
  simp_rw [h₂]
  unfold boxIntegral
  simpa only [zero_sub,show r-r/2=r/2 by ring] using
    intervalIntegral.integral_comp_sub_right
      (fun x => ∫ y in -(s/2)..s/2, ∫ z in -(t/2)..t/2, f x y z) (a := (0:ℝ)) (b := r) (r/2)

theorem d04UnbalancedEdgePolynomial_boxIntegral (p q : Fin 5 → ℝ)
    (a b c d : ℝ) (u : Fin 2 → ℝ) :
    (∫ y in (0:ℝ)..(a-u 0), ∫ z in (0:ℝ)..(b-u 1),
      ∫ t in (0:ℝ)..(c-(d-u 0-u 1)),
        d04UnbalancedEdgePolynomial p q (d04UnbalancedEdges a b c d u ![y,z,t])) =
      minusKernelBox p q (minusKernelT0 a b c d)
        (a-u 0) (b-u 1) (c-(d-u 0-u 1)) := by
  simp_rw [d04UnbalancedEdgePolynomial_centered]
  unfold minusKernelBox
  exact d04TripleInterval_translate (a-u 0) (b-u 1) (c-(d-u 0-u 1))
    (fun x y z => evalDegreeFour p (x+y+z-minusKernelT0 a b c d)*
      evalDegreeFour q (x+y+z+minusKernelT0 a b c d))

theorem d04UnbalancedEdgeIntegrand_edges (p q : Fin 5 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (a : Fin 4 → ℝ) (u : Fin 2 → ℝ) (y z t : ℝ) :
    d04UnbalancedEdgeIntegrand p q ρ
      (d04UnbalancedEdges (a 0) (a 1) (a 2) (a 3) u ![y,z,t]) =
      if u∈boundedSimplexSlice (a 0) (a 1) (a 2) (a 3) then
        (Icc 0 (a 0-u 0)).indicator (fun y =>
          (Icc 0 (a 1-u 1)).indicator (fun z =>
            (Icc 0 (a 2-(a 3-u 0-u 1))).indicator (fun t =>
              (∏ i, ρ i (a i))*d04UnbalancedEdgePolynomial p q
                (d04UnbalancedEdges (a 0) (a 1) (a 2) (a 3) u ![y,z,t])) t) z) y
      else 0 := by
  have hc := d04UnbalancedEdges_nonnegative_iff (a 0) (a 1) (a 2) (a 3) u ![y,z,t]
  have hi : (![y,z,t] : Fin 3 → ℝ)∈Icc (fun _ => 0)
      (d04UnbalancedResiduals (a 0) (a 1) (a 2) (a 3) u) ↔
      y∈Icc 0 (a 0-u 0) ∧ z∈Icc 0 (a 1-u 1) ∧
        t∈Icc 0 (a 2-(a 3-u 0-u 1)) := by
    simp [mem_Icc,Pi.le_def,Fin.forall_fin_succ,d04UnbalancedResiduals]
    tauto
  rw [hi] at hc
  unfold d04UnbalancedEdgeIntegrand
  simp only [Set.indicator_apply]
  rw [hc,d04UnbalancedEdgeProfile_edges]
  split_ifs <;> simp_all

theorem d04UnbalancedEdgeIntegrand_split_integral (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ) (u : Fin 2 → ℝ) :
    (∫ y : ℝ, ∫ z : ℝ, ∫ t : ℝ, d04UnbalancedEdgeIntegrand p q ρ
      (d04UnbalancedEdges (a 0) (a 1) (a 2) (a 3) u ![y,z,t])) =
      (boundedSimplexSlice (a 0) (a 1) (a 2) (a 3)).indicator
        (fun u => (∏ i, ρ i (a i))*minusKernelUniform p q
          (minusKernelT0 (a 0) (a 1) (a 2) (a 3))
          (a 0-u 0) (a 1-u 1) (a 2-(a 3-u 0-u 1))) u := by
  simp_rw [d04UnbalancedEdgeIntegrand_edges]
  by_cases hu : u∈boundedSimplexSlice (a 0) (a 1) (a 2) (a 3)
  · simp only [hu,ite_true,indicator_of_mem hu]
    have h₀ : 0≤a 0-u 0 := by linarith [hu.2.1]
    have h₁ : 0≤a 1-u 1 := by linarith [hu.2.2.1]
    have h₂ : 0≤a 2-(a 3-u 0-u 1) := by linarith [hu.2.2.2]
    have ht (y z : ℝ) :
        (∫ t : ℝ, (Icc 0 (a 0-u 0)).indicator (fun y =>
          (Icc 0 (a 1-u 1)).indicator (fun z =>
            (Icc 0 (a 2-(a 3-u 0-u 1))).indicator (fun t =>
              (∏ i, ρ i (a i))*d04UnbalancedEdgePolynomial p q
                (d04UnbalancedEdges (a 0) (a 1) (a 2) (a 3) u ![y,z,t])) t) z) y) =
        (Icc 0 (a 0-u 0)).indicator (fun y =>
          (Icc 0 (a 1-u 1)).indicator (fun z =>
            ∫ t in (0:ℝ)..(a 2-(a 3-u 0-u 1)),
              (∏ i, ρ i (a i))*d04UnbalancedEdgePolynomial p q
                (d04UnbalancedEdges (a 0) (a 1) (a 2) (a 3) u ![y,z,t])) z) y := by
      by_cases hy : y∈Icc 0 (a 0-u 0)
      · by_cases hz : z∈Icc 0 (a 1-u 1)
        · simp only [indicator_of_mem hy,indicator_of_mem hz]
          exact indicator_Icc_integral _ _ _ h₂
        · simp [Set.indicator_apply,hz]
      · simp [Set.indicator_apply,hy]
    simp_rw [ht]
    have hz (y : ℝ) :
        (∫ z : ℝ, (Icc 0 (a 0-u 0)).indicator (fun y =>
          (Icc 0 (a 1-u 1)).indicator (fun z =>
            ∫ t in (0:ℝ)..(a 2-(a 3-u 0-u 1)),
              (∏ i, ρ i (a i))*d04UnbalancedEdgePolynomial p q
                (d04UnbalancedEdges (a 0) (a 1) (a 2) (a 3) u ![y,z,t])) z) y) =
        (Icc 0 (a 0-u 0)).indicator (fun y =>
          ∫ z in (0:ℝ)..(a 1-u 1), ∫ t in (0:ℝ)..(a 2-(a 3-u 0-u 1)),
            (∏ i, ρ i (a i))*d04UnbalancedEdgePolynomial p q
              (d04UnbalancedEdges (a 0) (a 1) (a 2) (a 3) u ![y,z,t])) y := by
      by_cases hy : y∈Icc 0 (a 0-u 0)
      · simp only [indicator_of_mem hy]
        exact indicator_Icc_integral _ _ _ h₁
      · simp [Set.indicator_apply,hy]
    simp_rw [hz]
    rw [indicator_Icc_integral _ _ _ h₀]
    simp_rw [intervalIntegral.integral_const_mul]
    rw [d04UnbalancedEdgePolynomial_boxIntegral,minusKernelUniform_eq_box h₀ h₁ h₂]
  · simp [hu]

theorem d04UnbalancedEdgeIntegral_eq_profileKernel (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    (∫ x : D01EdgeSpace, d04UnbalancedEdgeIntegrand p q ρ x) =
      d04UnbalancedProfileKernel p q ρ := by
  rw [d04Edge_integral_fubini _ (d04UnbalancedEdgeIntegrand_integrable p q ρ A hρc hρcap)]
  simp_rw [d04UnbalancedEdgeIntegrand_split_integral]
  unfold d04UnbalancedProfileKernel denominatorMinusKernel
  apply integral_congr_ae
  filter_upwards [] with a
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u∈boundedSimplexSlice (a 0) (a 1) (a 2) (a 3)
  · simp [hu]
  · simp [hu]

end
end SixthMoment
