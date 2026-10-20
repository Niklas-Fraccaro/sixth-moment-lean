import SixthMoment.Certificate.Kernels.Unbalanced.DenominatorMinusLink


namespace SixthMoment

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 0

theorem translatedSimplexMonomialValue_zero (a b c : ℝ) (e₁ e₂ e₃ : ℕ) :
    translatedSimplexMonomialValue 0 a b c e₁ e₂ e₃ = 0 := by
  unfold translatedSimplexMonomialValue
  apply Finset.sum_eq_zero
  intro d₁ hd₁
  apply Finset.sum_eq_zero
  intro d₂ hd₂
  apply Finset.sum_eq_zero
  intro d₃ hd₃
  have h₁ := Finset.mem_range.mp hd₁
  have h₂ := Finset.mem_range.mp hd₂
  have h₃ := Finset.mem_range.mp hd₃
  have he : translatedSimplexExponent e₁ e₂ e₃ d₁ d₂ d₃ ≠ 0 := by
    unfold translatedSimplexExponent
    omega
  simp [zero_pow he]

theorem translatedSimplexMonomialValue_continuous_comp {α : Type*}
    [TopologicalSpace α] {H a b c : α → ℝ}
    (hH : Continuous H) (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (e₁ e₂ e₃ : ℕ) :
    Continuous (fun x => translatedSimplexMonomialValue (H x) (a x) (b x) (c x)
      e₁ e₂ e₃) := by
  unfold translatedSimplexMonomialValue
  apply continuous_finsetSum
  intro d₁ _
  apply continuous_finsetSum
  intro d₂ _
  apply continuous_finsetSum
  intro d₃ _
  fun_prop

theorem minusMaskEvenMomentValue_zero (m : ℕ) (mask : Fin 8) (a b c : ℝ) :
    minusMaskEvenMomentValue m mask a b c 0 = 0 := by
  simp [minusMaskEvenMomentValue, translatedSimplexMonomialValue_zero]

theorem minusMaskEvenMomentValue_continuous_comp {α : Type*}
    [TopologicalSpace α] {H a b c : α → ℝ}
    (hH : Continuous H) (ha : Continuous a) (hb : Continuous b) (hc : Continuous c)
    (m : ℕ) (mask : Fin 8) :
    Continuous (fun x => minusMaskEvenMomentValue m mask (a x) (b x) (c x) (H x)) := by
  unfold minusMaskEvenMomentValue
  apply continuous_const.mul
  apply continuous_finsetSum
  intro l₁ _
  apply continuous_finsetSum
  intro l₂ _
  apply continuous_finsetSum
  intro l₃ _
  by_cases hl : l₁.val + l₂.val + l₃.val = m
  · simp only [hl, ite_true]
    apply Continuous.div_const
    apply translatedSimplexMonomialValue_continuous_comp hH
    all_goals unfold minusMaskCap; split_ifs <;> fun_prop
  · simp only [hl, ite_false]
    exact continuous_const

theorem minusMaskEvenMomentValue_cutoff_eq_positivePart
    (m : ℕ) (mask : Fin 8) (a b c H : ℝ) :
    (if H ≤ 0 then 0 else minusMaskEvenMomentValue m mask a b c H) =
      minusMaskEvenMomentValue m mask a b c (max H 0) := by
  by_cases hH : H ≤ 0
  · simp [hH, minusMaskEvenMomentValue_zero]
  · simp [hH, max_eq_left (le_of_lt (lt_of_not_ge hH))]

noncomputable def denominatorMinusContinuousEvaluator (p q : Fin 5 → ℝ)
    (a b c d : ℝ) : ℝ :=
  ∑ m : Fin 5,
    minusBoxCoefficient p q (minusKernelT0 a b c d) (minusEvenIndex m) *
      ∑ mask : Fin 8, simplexMaskSign mask *
        minusMaskEvenMomentValue m.val mask a b c
          (max (minusKernelH a b c d - simplexMaskShift a b c mask) 0)

theorem denominatorMinusKernel_eq_continuousEvaluator (p q : Fin 5 → ℝ)
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (d : ℝ) :
    denominatorMinusKernel p q a b c d =
      denominatorMinusContinuousEvaluator p q a b c d := by
  rw [denominatorMinusKernel_polynomial]
  simp_rw [boundedSimplexSlice_minusBoxEvenMoment_masks ha hb hc,
    minusMaskEvenMomentValue_cutoff_eq_positivePart]
  rfl

theorem denominatorMinusContinuousEvaluator_continuous_comp {α : Type*}
    [TopologicalSpace α] (p q : Fin 5 → ℝ) {a b c d : α → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d) :
    Continuous (fun x => denominatorMinusContinuousEvaluator p q
      (a x) (b x) (c x) (d x)) := by
  unfold denominatorMinusContinuousEvaluator
  apply continuous_finsetSum
  intro m _
  apply Continuous.mul
  · apply (minusBoxCoefficient_continuous p q (minusEvenIndex m)).comp
    unfold minusKernelT0
    fun_prop
  · apply continuous_finsetSum
    intro mask _
    apply continuous_const.mul
    apply minusMaskEvenMomentValue_continuous_comp
    · unfold minusKernelH simplexMaskShift
      split_ifs <;> fun_prop
    · exact ha
    · exact hb
    · exact hc

theorem denominatorMinusKernel_continuousOn (p q : Fin 5 → ℝ) :
    ContinuousOn (fun v : Fin 4 → ℝ =>
      denominatorMinusKernel p q (v 0) (v 1) (v 2) (v 3))
      {v | 0 ≤ v 0 ∧ 0 ≤ v 1 ∧ 0 ≤ v 2} := by
  have he : Continuous (fun v : Fin 4 → ℝ =>
      denominatorMinusContinuousEvaluator p q (v 0) (v 1) (v 2) (v 3)) :=
    denominatorMinusContinuousEvaluator_continuous_comp p q
      (continuous_apply 0) (continuous_apply 1) (continuous_apply 2) (continuous_apply 3)
  apply he.continuousOn.congr
  intro v hv
  exact denominatorMinusKernel_eq_continuousEvaluator p q hv.1 hv.2.1 hv.2.2 (v 3)

theorem denominatorMinusKernel_continuous_comp {α : Type*} [TopologicalSpace α]
    (p q : Fin 5 → ℝ) {a b c d : α → ℝ}
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) (hd : Continuous d)
    (ha₀ : ∀ x, 0 ≤ a x) (hb₀ : ∀ x, 0 ≤ b x) (hc₀ : ∀ x, 0 ≤ c x) :
    Continuous (fun x => denominatorMinusKernel p q (a x) (b x) (c x) (d x)) := by
  have he := denominatorMinusContinuousEvaluator_continuous_comp p q ha hb hc hd
  apply he.congr
  intro x
  exact (denominatorMinusKernel_eq_continuousEvaluator p q
    (ha₀ x) (hb₀ x) (hc₀ x) (d x)).symm

theorem denominatorMinusKernel_tendsto_of_nonnegative {α : Type*}
    {l : Filter α} (p q : Fin 5 → ℝ) {a b c d : α → ℝ} {A B C D : ℝ}
    (ha : Filter.Tendsto a l (nhds A)) (hb : Filter.Tendsto b l (nhds B))
    (hc : Filter.Tendsto c l (nhds C)) (hd : Filter.Tendsto d l (nhds D))
    (ha₀ : ∀ᶠ x in l, 0 ≤ a x) (hb₀ : ∀ᶠ x in l, 0 ≤ b x)
    (hc₀ : ∀ᶠ x in l, 0 ≤ c x) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    Filter.Tendsto (fun x => denominatorMinusKernel p q (a x) (b x) (c x) (d x))
      l (nhds (denominatorMinusKernel p q A B C D)) := by
  have hecont : Continuous (fun v : ℝ × ℝ × ℝ × ℝ =>
      denominatorMinusContinuousEvaluator p q v.1 v.2.1 v.2.2.1 v.2.2.2) :=
    denominatorMinusContinuousEvaluator_continuous_comp p q
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have he := (hecont.tendsto (A, B, C, D)).comp
    (ha.prodMk_nhds (hb.prodMk_nhds (hc.prodMk_nhds hd)))
  change Filter.Tendsto (fun x => denominatorMinusContinuousEvaluator p q
    (a x) (b x) (c x) (d x)) l
      (nhds (denominatorMinusContinuousEvaluator p q A B C D)) at he
  rw [← denominatorMinusKernel_eq_continuousEvaluator p q hA hB hC D] at he
  apply he.congr'
  filter_upwards [ha₀, hb₀, hc₀] with x hax hbx hcx
  exact (denominatorMinusKernel_eq_continuousEvaluator p q hax hbx hcx (d x)).symm

end SixthMoment
