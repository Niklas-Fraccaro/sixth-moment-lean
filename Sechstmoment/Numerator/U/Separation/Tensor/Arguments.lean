import Sechstmoment.Numerator.U.Separation.Frequency.ActualFarIntegral
import Sechstmoment.Numerator.U.Separation.Frequency.SixComposition
import Sechstmoment.Numerator.U.Separation.SixTensorSource
import Sechstmoment.Numerator.U.Separation.Tensor.MellinFactor

namespace Sechstmoment
open Complex Real Source Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem a03SixSourceArguments_eq (q : QuadraticScales) (n : Fin 7 → ℕ) :
    a03SixSourceArguments q n =
      ![(n 1 : ℝ)/q.B, (n 6 : ℝ)/q.H, (n 2 : ℝ)/q.M₁,
        (n 3 : ℝ)/q.M₂, (n 4 : ℝ)/q.N₁, (n 5 : ℝ)/q.N₂] := rfl

theorem a03SixTensorLogPoint_apply (x : Fin 6 → ℝ) (j : Fin 6) :
    a03SixTensorLogPoint x j = Real.log (x j) := rfl

theorem a03SixGapLinear_logPoint_exp (x : Fin 6 → ℝ)
    (hx : ∀ j, 0 < x j) :
    Real.exp (a03SixGapLinear (a03SixTensorLogPoint x)) =
      x 1/(x 0*x 4*x 5) := by
  rw [a03SixGapLinear_apply]
  simp only [a03SixTensorLogPoint_apply, Real.exp_sub, Real.exp_log (hx _)]
  ring

theorem a03TensorMellinFactor_logPoint (α : MomentShifts) (z : ℂ)
    (x : Fin 6 → ℝ) (hx : ∀ j, 0 < x j) :
    a03TensorMellinFactor α z (a03SixTensorLogPoint x) =
      ∏ i : Fin 4, (x i.succ.succ : ℂ)^(-(1/2+α i+z)) := by
  rw [a03TensorMellinFactor_eq_exp, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hx i.succ.succ).ne'),
    ← Complex.ofReal_log (hx i.succ.succ).le]
  congr 1
  rw [a03SixTensorLogPoint_apply, mul_comm]

theorem a03SixSourceArguments_positive (q : QuadraticScales) (n : Fin 7 → ℕ)
    (hq : ∀ j, 0 < q.size j) (hn : n ∈ quadraticIndexSet q) :
    ∀ j, 0 < a03SixSourceArguments q n j := by
  have hp (i : Fin 7) : 0 < (n i : ℝ) := by
    have h := (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hn i)).1
    exact_mod_cast h
  intro j
  fin_cases j
  · exact div_pos (hp 1) (hq 1)
  · exact div_pos (hp 6) (hq 6)
  · exact div_pos (hp 2) (hq 2)
  · exact div_pos (hp 3) (hq 3)
  · exact div_pos (hp 4) (hq 4)
  · exact div_pos (hp 5) (hq 5)

theorem a03SixSourceArguments_smooth_support (q : QuadraticScales) (n : Fin 7 → ℕ)
    (hβ : rectangularSmoothBlockWeight ((n 1 : ℝ)/q.B) ≠ 0)
    (hW : (∏ j : Fin 5, (rectangularSmoothBlockWeight
      (rectangularWeightArguments q n j) : ℂ)) ≠ 0) :
    ∀ j, a03SixSourceArguments q n j ∈ Icc 1 2 := by
  have hw (j : Fin 5) : rectangularSmoothBlockWeight
      (rectangularWeightArguments q n j) ≠ 0 := by
    intro h
    apply hW
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp only [h, Complex.ofReal_zero])
  intro j
  cases j using Fin.cases with
  | zero => exact rectangularSmoothBlockWeight_tsupport (subset_tsupport _ hβ)
  | succ j => exact rectangularSmoothBlockWeight_tsupport (subset_tsupport _ (hw j))

theorem a03SixSourceArguments_gap_ratio_of_positive (q : QuadraticScales) (n : Fin 7 → ℕ)
    (hq : ∀ j, 0 < q.size j) (hx : ∀ j, 0 < a03SixSourceArguments q n j) (s : ℝ) :
    s*(q.H/(q.B*q.N₁*q.N₂))*
      Real.exp (a03SixGapLinear (a03SixTensorLogPoint (a03SixSourceArguments q n))) =
      s*(n 6 : ℝ)/((n 1 : ℝ)*n 4*n 5) := by
  rw [a03SixGapLinear_logPoint_exp _ hx,
    a03SixSourceArguments_eq]
  change s*(q.H/(q.B*q.N₁*q.N₂))*((n 6 : ℝ)/q.H/
    (((n 1 : ℝ)/q.B)*((n 4 : ℝ)/q.N₁)*((n 5 : ℝ)/q.N₂))) = _
  have hB : q.B ≠ 0 := (by simpa [QuadraticScales.size] using hq 1 : 0 < q.B).ne'
  have hH : q.H ≠ 0 := (by simpa [QuadraticScales.size] using hq 6 : 0 < q.H).ne'
  have hN₁ : q.N₁ ≠ 0 := (by simpa [QuadraticScales.size] using hq 4 : 0 < q.N₁).ne'
  have hN₂ : q.N₂ ≠ 0 := (by simpa [QuadraticScales.size] using hq 5 : 0 < q.N₂).ne'
  field_simp [hB,hH,hN₁,hN₂]

theorem a03SixSourceArguments_gap_ratio (q : QuadraticScales) (n : Fin 7 → ℕ)
    (hq : ∀ j, 0 < q.size j) (hn : n ∈ quadraticIndexSet q) (s : ℝ) :
    s*(q.H/(q.B*q.N₁*q.N₂))*
      Real.exp (a03SixGapLinear (a03SixTensorLogPoint (a03SixSourceArguments q n))) =
      s*(n 6 : ℝ)/((n 1 : ℝ)*n 4*n 5) :=
  a03SixSourceArguments_gap_ratio_of_positive q n hq
    (a03SixSourceArguments_positive q n hq hn) s

theorem a03SixSourceArguments_signed_frequency (positive : Bool) (T : ℝ)
    (q : QuadraticScales) (n : Fin 7 → ℕ)
    (hq : ∀ j, 0 < q.size j) (hn : n ∈ quadraticIndexSet q) :
    a03RealLogGapSymbol T (q.H/(q.B*q.N₁*q.N₂)) (rectangularGapSign positive)
      (a03SixGapLinear (a03SixTensorLogPoint (a03SixSourceArguments q n))) =
      T*Real.log (1+rectangularGapSign positive*(n 6 : ℝ)/((n 1 : ℝ)*n 4*n 5)) := by
  unfold a03RealLogGapSymbol
  rw [a03SixSourceArguments_gap_ratio q n hq hn]

theorem a03SixSourceArguments_actual_tuple (A B H : ℝ) (k n : Fin 4 → ℕ)
    (a b h : ℕ) :
    a03SixSourceArguments (phaseActualScales A B H k) (rectangularAFESourceTuple a b n h) =
      ![(b : ℝ)/B, (h : ℝ)/H,
        (n 0+1 : ℝ)/rectangularAFESmoothScale (k 0),
        (n 1+1 : ℝ)/rectangularAFESmoothScale (k 1),
        (n 2+1 : ℝ)/rectangularAFESmoothScale (k 2),
        (n 3+1 : ℝ)/rectangularAFESmoothScale (k 3)] := by
  rw [a03SixSourceArguments_eq]
  simp [phaseActualScales, rectangularAFESourceTuple]

theorem a03_source_product_ratio_signed_relation (positive : Bool) (n : Fin 7 → ℕ)
    (hr : signedQuadraticRelation positive n)
    (hd : (n 1 : ℝ)*n 4*n 5 ≠ 0) :
    ((n 0 : ℝ)*n 2*n 3)/((n 1 : ℝ)*n 4*n 5) =
      1+rectangularGapSign positive*(n 6 : ℝ)/((n 1 : ℝ)*n 4*n 5) := by
  have hs : (n 0 : ℝ)*n 2*n 3-(n 1 : ℝ)*n 4*n 5 =
      rectangularGapSign positive*(n 6 : ℝ) := by
    cases positive <;> simp [signedQuadraticRelation, rectangularGapSign] at hr ⊢
    all_goals exact_mod_cast hr
  rw [show (n 0 : ℝ)*n 2*n 3 =
    (n 1 : ℝ)*n 4*n 5+rectangularGapSign positive*(n 6 : ℝ) by linear_combination hs,
    add_div, div_self hd]

theorem a03_actual_product_ratio_signed_gap (positive : Bool) (a b : ℕ)
    (hb : 0 < b) (n : Fin 4 → ℕ)
    (hn : if positive then rectangularPositiveQuadGap a b n
      else rectangularNegativeQuadGap a b n) :
    phaseActualProductRatio a b n =
      1+rectangularGapRatio positive b (rectangularAFEGap positive a b n) n := by
  have hd : (b : ℝ)*(n 2+1)*(n 3+1) ≠ 0 := by positivity
  have h := a03_source_product_ratio_signed_relation positive
    (rectangularAFESourceTuple a b n (rectangularAFEGap positive a b n))
    (rectangular_AFE_gap_source_relation positive a b n hn)
    (by simpa [rectangularAFESourceTuple] using hd)
  simpa [phaseActualProductRatio, rectangularGapRatio, rectangularAFESourceTuple,
    Nat.cast_mul] using h

theorem phaseActualScales_positive {A B H : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hH : 0 < H) (k : Fin 4 → ℕ) :
    ∀ j, 0 < (phaseActualScales A B H k).size j := by
  have hscale (i : Fin 4) : 0 < rectangularAFESmoothScale (k i) := by
    unfold rectangularAFESmoothScale
    positivity
  intro j
  fin_cases j
  · exact hA
  · exact hB
  · exact hscale 0
  · exact hscale 1
  · exact hscale 2
  · exact hscale 3
  · exact hH

theorem a03SixSourceArguments_actual_positive {A B H : ℝ}
    (hB : 0 < B) (hH : 0 < H) (k n : Fin 4 → ℕ)
    {a b h : ℕ} (hb : 0 < b) (hh : 0 < h) :
    ∀ j, 0 < a03SixSourceArguments (phaseActualScales A B H k)
      (rectangularAFESourceTuple a b n h) j := by
  rw [a03SixSourceArguments_actual_tuple]
  intro j
  have hscale (i : Fin 4) : 0 < rectangularAFESmoothScale (k i) := by
    unfold rectangularAFESmoothScale
    positivity
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hh' : 0 < (h : ℝ) := by exact_mod_cast hh
  fin_cases j
  · exact div_pos hb' hB
  · exact div_pos hh' hH
  · exact div_pos (by positivity) (hscale 0)
  · exact div_pos (by positivity) (hscale 1)
  · exact div_pos (by positivity) (hscale 2)
  · exact div_pos (by positivity) (hscale 3)

theorem a03_actual_gap_frequency_identity (positive : Bool) (T : ℝ) {A B H : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hH : 0 < H)
    (k n : Fin 4 → ℕ) (a b : ℕ) (hb : 0 < b)
    (hn : if positive then rectangularPositiveQuadGap a b n
      else rectangularNegativeQuadGap a b n) :
    a03RealLogGapSymbol T
      (H/(B*rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3)))
      (rectangularGapSign positive)
      (a03SixGapLinear (a03SixTensorLogPoint
        (a03SixSourceArguments (phaseActualScales A B H k)
          (rectangularAFESourceTuple a b n (rectangularAFEGap positive a b n))))) =
      T*Real.log (phaseActualProductRatio a b n) := by
  unfold a03RealLogGapSymbol
  have hratio := a03SixSourceArguments_gap_ratio_of_positive
    (phaseActualScales A B H k)
    (rectangularAFESourceTuple a b n (rectangularAFEGap positive a b n))
    (phaseActualScales_positive hA hB hH k)
    (a03SixSourceArguments_actual_positive hB hH k n hb
      (rectangular_AFE_gap_pos positive a b n hn)) (rectangularGapSign positive)
  have hratio' : rectangularGapSign positive *
      (H/(B*rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3))) *
      Real.exp (a03SixGapLinear (a03SixTensorLogPoint
        (a03SixSourceArguments (phaseActualScales A B H k)
          (rectangularAFESourceTuple a b n (rectangularAFEGap positive a b n))))) =
      rectangularGapRatio positive b (rectangularAFEGap positive a b n) n := by
    simpa [phaseActualScales, rectangularAFESourceTuple, rectangularGapRatio, Nat.cast_mul]
      using hratio
  rw [hratio', ← a03_actual_product_ratio_signed_gap positive a b hb n hn]

end
end Sechstmoment
