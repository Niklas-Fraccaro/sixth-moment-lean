import Sechstmoment.Numerator.U.Reconstruction.TensorActualSourceEndpoint
import Sechstmoment.Numerator.U.Separation.Tensor.PhysicalKernel

/-! The literal signed source index is the actual finite amplifier/AFE
index, with its positive natural gap determined by the integer relation. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology FourierTransform
open Classical
noncomputable section
set_option maxHeartbeats 1000000

def a03SourceQuadProjection (n : Fin 7→ℕ) : Fin 4→ℕ :=
  ![n 2-1,n 3-1,n 4-1,n 5-1]

theorem a03SourceQuadProjection_sourceTuple (p q h : ℕ) (n : Fin 4→ℕ) :
    a03SourceQuadProjection (rectangularAFESourceTuple p q n h)=n := by
  ext j
  fin_cases j <;> simp [a03SourceQuadProjection,rectangularAFESourceTuple]

theorem a03SourceQuadProjection_reconstruct (n : Fin 7→ℕ) (hn : ∀ j,1≤n j) :
    rectangularAFESourceTuple (n 0) (n 1) (a03SourceQuadProjection n) (n 6)=n := by
  ext j
  fin_cases j <;> simp [a03SourceQuadProjection,rectangularAFESourceTuple]
  all_goals have := hn 2; have := hn 3; have := hn 4; have := hn 5; omega

theorem phaseActualAmplifierCoefficient_nonzero_integer_cap {a T A : ℝ}
    (hT : 1<T) (f : ℝ→ℝ) (hf : SmoothInteriorProfile a f) {n : ℕ}
    (_hn : 0<n) (hcoef : phaseActualAmplifierCoefficient T f A n≠0) :
    (n:ℝ)≤T^a := by
  have hfn : f (Real.log (n:ℝ)/Real.log T)≠0 := by
    intro h
    apply hcoef
    simp only [phaseActualAmplifierCoefficient,h,Complex.ofReal_zero,mul_zero,zero_mul]
  have hlog := Real.log_pos hT
  have hupper := (hf.2.2 (subset_tsupport f hfn)).2.le
  apply Real.le_rpow_of_log_le (zero_lt_one.trans hT)
  exact (div_le_iff₀ hlog).mp hupper

theorem a03SourceQuadProjection_selected {q : QuadraticScales} (positive : Bool)
    (n : Fin 7→ℕ) (hn : n∈quadraticIndexSet q) (hr : signedQuadraticRelation positive n) :
    (if positive then rectangularPositiveQuadGap (n 0) (n 1) (a03SourceQuadProjection n)
      else rectangularNegativeQuadGap (n 0) (n 1) (a03SourceQuadProjection n)) ∧
      rectangularAFESourceTuple (n 0) (n 1) (a03SourceQuadProjection n)
        (rectangularAFEGap positive (n 0) (n 1) (a03SourceQuadProjection n))=n := by
  have hp : ∀ j,1≤n j := fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn j)).1
  have he := a03SourceQuadProjection_reconstruct n hp
  have hrel : signedQuadraticRelation positive
      (rectangularAFESourceTuple (n 0) (n 1) (a03SourceQuadProjection n) (n 6)) := by rw [he]; exact hr
  have hgap : 0<(n 6:ℤ) := by exact_mod_cast (show 0<n 6 by have := hp 6; omega)
  have hselect : if positive then rectangularPositiveQuadGap (n 0) (n 1) (a03SourceQuadProjection n)
      else rectangularNegativeQuadGap (n 0) (n 1) (a03SourceQuadProjection n) := by
    cases positive <;> simp only [Bool.false_eq_true,ite_false,ite_true] at *
    · unfold rectangularNegativeQuadGap
      simp [signedQuadraticRelation,rectangularAFESourceTuple] at hrel
      exact_mod_cast (by push_cast; linarith : (n 0:ℤ)*((a03SourceQuadProjection n 0+1):ℕ)*((a03SourceQuadProjection n 1+1):ℕ)<
        (n 1:ℤ)*((a03SourceQuadProjection n 2+1):ℕ)*((a03SourceQuadProjection n 3+1):ℕ))
    · unfold rectangularPositiveQuadGap
      simp [signedQuadraticRelation,rectangularAFESourceTuple] at hrel
      exact_mod_cast (by push_cast; linarith : (n 1:ℤ)*((a03SourceQuadProjection n 2+1):ℕ)*((a03SourceQuadProjection n 3+1):ℕ)<
        (n 0:ℤ)*((a03SourceQuadProjection n 0+1):ℕ)*((a03SourceQuadProjection n 1+1):ℕ))
  have hh := (rectangular_AFE_gap_source_unique positive (n 0) (n 1)
    (a03SourceQuadProjection n) hselect (n 6)).mp hrel
  exact ⟨hselect,by rw [←hh]; exact he⟩

/-- The exact literal nonzero source terms are reindexed by the genuine
finite amplifier ranges and smooth AFE box. The tensor is arbitrary. -/
theorem a03_actual_source_signed_finite_reindex {a b T A B H : ℝ}
    (hT : 1<T) (hA : 0<A) (hB : 0<B) (hH : 0<H)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (k : Fin 4→ℕ) (positive : Bool) (F : (Fin 7→ℕ)→ℂ) :
    (∑ n∈quadraticIndexSet (phaseActualScales A B H k),
      if signedQuadraticRelation positive n then
        phaseActualAmplifierCoefficient T f A (n 0)*phaseActualAmplifierCoefficient T g B (n 1)*
          (∏ j : Fin 5, (rectangularSmoothBlockWeight
            (rectangularWeightArguments (phaseActualScales A B H k) n j):ℂ))*F n else 0)=
      ∑ i∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),
        if (if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
          else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2) then
          let n := rectangularAFESourceTuple (i.1.1+1) (i.1.2+1) i.2
            (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2)
          phaseActualAmplifierCoefficient T f A (n 0)*phaseActualAmplifierCoefficient T g B (n 1)*
            (∏ j : Fin 5, (rectangularSmoothBlockWeight
              (rectangularWeightArguments (phaseActualScales A B H k) n j):ℂ))*F n else 0 := by
  let q := phaseActualScales A B H k
  let S := fun n : Fin 7→ℕ => if signedQuadraticRelation positive n then
    phaseActualAmplifierCoefficient T f A (n 0)*phaseActualAmplifierCoefficient T g B (n 1)*
      (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments q n j):ℂ))*F n else 0
  let D := fun i : (ℕ×ℕ)×(Fin 4→ℕ) =>
    if (if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
      else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2) then
      let n := rectangularAFESourceTuple (i.1.1+1) (i.1.2+1) i.2
        (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2)
      phaseActualAmplifierCoefficient T f A (n 0)*phaseActualAmplifierCoefficient T g B (n 1)*
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments q n j):ℂ))*F n else 0
  have hrel (n : Fin 7→ℕ) (hSn : S n≠0) : signedQuadraticRelation positive n := by
    by_contra h
    exact hSn (by simp only [S,h,ite_false])
  have hpos (n : Fin 7→ℕ) (hn : n∈quadraticIndexSet q) : ∀ j,1≤n j :=
    fun j => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn j)).1
  have hfactors (n : Fin 7→ℕ) (hSn : S n≠0) :
      phaseActualAmplifierCoefficient T f A (n 0)≠0 ∧
      phaseActualAmplifierCoefficient T g B (n 1)≠0 ∧
      (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments q n j):ℂ))≠0 := by
    have hn := hSn
    simp only [S,hrel n hSn,ite_true,mul_ne_zero_iff] at hn
    exact ⟨hn.1.1.1,hn.1.1.2,hn.1.2⟩
  have hreconstruct (n : Fin 7→ℕ) (hn : n∈quadraticIndexSet q) (hSn : S n≠0) :=
    a03SourceQuadProjection_selected positive n hn (hrel n hSn)
  change (∑ n∈quadraticIndexSet q,S n)=_
  change _=∑ i∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),D i
  apply Finset.sum_bij_ne_zero (fun n _ _ => ((n 0-1,n 1-1),a03SourceQuadProjection n))
  · intro n hn hSn
    obtain ⟨ha,hb,_hw⟩ := hfactors n hSn
    have hp := hpos n hn
    have haCap := Nat.le_floor (phaseActualAmplifierCoefficient_nonzero_integer_cap hT f hf
      (by have := hp 0; omega) ha)
    have hbCap := Nat.le_floor (phaseActualAmplifierCoefficient_nonzero_integer_cap hT g hg
      (by have := hp 1; omega) hb)
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by change n 0-1<⌊T^a⌋₊; have := hp 0; omega),
      Finset.mem_range.mpr (by change n 1-1<⌊T^b⌋₊; have := hp 1; omega)⟩,?_⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    have h2 : 1≤n 2 ∧ n 2≤⌊2*rectangularAFESmoothScale (k 0)⌋₊ := by
      simpa [q,phaseActualScales,QuadraticScales.size] using
        (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn 2))
    have h3 : 1≤n 3 ∧ n 3≤⌊2*rectangularAFESmoothScale (k 1)⌋₊ := by
      simpa [q,phaseActualScales,QuadraticScales.size] using
        (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn 3))
    have h4 : 1≤n 4 ∧ n 4≤⌊2*rectangularAFESmoothScale (k 2)⌋₊ := by
      simpa [q,phaseActualScales,QuadraticScales.size] using
        (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn 4))
    have h5 : 1≤n 5 ∧ n 5≤⌊2*rectangularAFESmoothScale (k 3)⌋₊ := by
      simpa [q,phaseActualScales,QuadraticScales.size] using
        (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn 5))
    fin_cases j
    · change n 2-1∈Finset.range ⌊2*rectangularAFESmoothScale (k 0)⌋₊
      exact Finset.mem_range.mpr (by omega)
    · change n 3-1∈Finset.range ⌊2*rectangularAFESmoothScale (k 1)⌋₊
      exact Finset.mem_range.mpr (by omega)
    · change n 4-1∈Finset.range ⌊2*rectangularAFESmoothScale (k 2)⌋₊
      exact Finset.mem_range.mpr (by omega)
    · change n 5-1∈Finset.range ⌊2*rectangularAFESmoothScale (k 3)⌋₊
      exact Finset.mem_range.mpr (by omega)
  · intro n hn hSn m hm hSm he
    have hnrec := (hreconstruct n hn hSn).2
    have hmrec := (hreconstruct m hm hSm).2
    have h0 : n 0=m 0 := by
      have h := congrArg (fun i : (ℕ×ℕ)×(Fin 4→ℕ) => i.1.1) he
      have := hpos n hn 0
      have := hpos m hm 0
      dsimp only at h
      omega
    have h1 : n 1=m 1 := by
      have h := congrArg (fun i : (ℕ×ℕ)×(Fin 4→ℕ) => i.1.2) he
      have := hpos n hn 1
      have := hpos m hm 1
      dsimp only at h
      omega
    have hq := congrArg (fun i : (ℕ×ℕ)×(Fin 4→ℕ) => i.2) he
    change a03SourceQuadProjection n=a03SourceQuadProjection m at hq
    rw [←hnrec,←hmrec,h0,h1,hq]
  · intro i hi hDi
    have hsel : if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
        else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2 := by
      by_contra h
      exact hDi (by simp only [D,h,ite_false])
    let n := rectangularAFESourceTuple (i.1.1+1) (i.1.2+1) i.2
      (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2)
    have hprod : phaseActualAmplifierCoefficient T f A (n 0)*phaseActualAmplifierCoefficient T g B (n 1)*
        (∏ j : Fin 5, (rectangularSmoothBlockWeight (rectangularWeightArguments q n j):ℂ))*F n≠0 := by
      simpa only [D,hsel,ite_true] using hDi
    have hha : phaseActualAmplifierCoefficient T f A (i.1.1+1)≠0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1).1).1
    have hhb : phaseActualAmplifierCoefficient T g B (i.1.2+1)≠0 :=
      (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1).1).2
    have hweights := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hprod).1).2
    have hgap : rectangularSmoothBlockWeight
        ((rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2:ℝ)/H)≠0 := by
      have h := hweights 0 (Finset.mem_univ _)
      simpa [n,q,rectangularWeightArguments,rectangularAFESourceTuple,phaseActualScales] using h
    have hAFE : rectangularAFESmoothWeight k i.2≠0 := by
      rw [rectangularAFESmoothWeight_scaled_arguments]
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      have h1 := hweights 1 (Finset.mem_univ _)
      have h2 := hweights 2 (Finset.mem_univ _)
      have h3 := hweights 3 (Finset.mem_univ _)
      have h4 := hweights 4 (Finset.mem_univ _)
      simp [n,q,rectangularWeightArguments,rectangularAFESourceTuple,phaseActualScales] at h1 h2 h3 h4
      fin_cases j <;> first | simpa using h1 | simpa using h2 | simpa using h3 | simpa using h4
    have hn : n∈quadraticIndexSet q := phase_actual_source_tuple_index T A B H f g hA hB hH
      k i.2 (i.1.1+1) (i.1.2+1) (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2) hha hhb hAFE hgap
    have hnrel : signedQuadraticRelation positive n := rectangular_AFE_gap_source_relation positive (i.1.1+1) (i.1.2+1) i.2 hsel
    refine ⟨n,hn,?_,?_⟩
    · simpa only [S,hnrel,ite_true] using hprod
    · rw [show a03SourceQuadProjection n=i.2 by exact a03SourceQuadProjection_sourceTuple _ _ _ _]
      simp only [n,rectangularAFESourceTuple,Matrix.cons_val_zero,Matrix.cons_val_one,Nat.add_sub_cancel]
  · intro n hn hSn
    obtain ⟨hselect,hrec⟩ := hreconstruct n hn hSn
    have hp := hpos n hn
    have hn0 : n 0-1+1=n 0 := by have := hp 0; omega
    have hn1 : n 1-1+1=n 1 := by have := hp 1; omega
    simp only [D,hn0,hn1,hselect,ite_true,hrec,S,hrel n hSn]
/-- The actual main physical tensor sum is the literal finite sum of
its genuine localized time integrals. -/
theorem a03_actual_main_physical_source_finite_reindex {a b T A B H : ℝ}
    (hT : 1<T) (hA : 0<A) (hB : 0<B) (hH : 0<H)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (σ α : MomentShifts) (c v : ℝ) (k : Fin 4→ℕ) (positive : Bool) :
    (T:ℂ)*(∏ j : Fin 4, (rectangularAFESmoothScale (k j):ℂ)^(-(1/2+α j+((c:ℂ)+(v:ℂ)*I))))*
      a03EndpointPhysicalTensorSum (a03ActualTensorRawKernel (fun x => (Φ x:ℂ)) c)
        positive T A B H σ α v f g k=
      ∑ i∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),
        if (if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
          else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2) then
          ∫ t : ℝ, phaseActualKernelSummand T A B H f g Φ
            (polarPoleKiller T σ) α i.1.1 i.1.2 t k i.2
              (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2) ((c:ℂ)+(v:ℂ)*I) else 0 := by
  unfold a03EndpointPhysicalTensorSum
  rw [a03_actual_source_signed_finite_reindex hT hA hB hH f g hf hg k positive,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hsel : if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
    else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2
  · simp only [hsel,ite_true]
    rw [a03_actual_kernel_time_raw_tensor_identity positive (zero_lt_one.trans hT) hA hB hH f g Φ σ α c v i.1.1 i.1.2 k i.2 hsel]
    simp only [rectangularAFESourceTuple,Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  · simp only [hsel,ite_false,mul_zero]

/-- The actual dual physical tensor sum is the literal finite sum of
its genuine localized time integrals. -/
theorem a03_actual_dual_physical_source_finite_reindex {a b T A B H : ℝ}
    (hT : 1<T) (hA : 0<A) (hB : 0<B) (hH : 0<H)
    (f g Φ : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (σ α : MomentShifts) (c v : ℝ) (k : Fin 4→ℕ) (positive : Bool) :
    (T:ℂ)*(∏ j : Fin 4, (rectangularAFESmoothScale (k j):ℂ)^(-(1/2+α j+((c:ℂ)+(v:ℂ)*I))))*
      a03EndpointPhysicalTensorSum (a03ActualDualTensorRawKernel (fun x => (Φ x:ℂ)) c)
        positive T A B H σ α v f g k=
      ∑ i∈((Finset.range ⌊T^a⌋₊).product (Finset.range ⌊T^b⌋₊)).product (rectangularAFESmoothBox k),
        if (if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
          else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2) then
          ∫ t : ℝ, bblrDualMultiplier t (rawMomentShifts T σ)*
            phaseActualKernelSummand T A B H f g Φ
            (polarPoleKiller T σ) α i.1.1 i.1.2 t k i.2
              (rectangularAFEGap positive (i.1.1+1) (i.1.2+1) i.2) ((c:ℂ)+(v:ℂ)*I) else 0 := by
  unfold a03EndpointPhysicalTensorSum
  rw [a03_actual_source_signed_finite_reindex hT hA hB hH f g hf hg k positive,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hsel : if positive then rectangularPositiveQuadGap (i.1.1+1) (i.1.2+1) i.2
    else rectangularNegativeQuadGap (i.1.1+1) (i.1.2+1) i.2
  · simp only [hsel,ite_true]
    rw [a03_actual_kernel_dual_time_raw_tensor_identity positive (zero_lt_one.trans hT) hA hB hH f g Φ σ α c v i.1.1 i.1.2 k i.2 hsel]
    simp only [rectangularAFESourceTuple,Matrix.cons_val_zero,Matrix.cons_val_one]
    ring
  · simp only [hsel,ite_false,mul_zero]

end
end Sechstmoment
