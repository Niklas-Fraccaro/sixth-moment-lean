import SixthMoment.Analysis.Integration.BoxUniformMoments
import SixthMoment.Certificate.Kernels.Balanced.Inner
import SixthMoment.Certificate.Kernels.Unbalanced.InclusionExclusion


namespace SixthMoment
open MeasureTheory

noncomputable def minusKernelH (a b c d : ℝ) : ℝ := a+b+c-d
noncomputable def minusKernelT0 (a b c d : ℝ) : ℝ := (1-(a+b+c-d))/2

noncomputable def minusKernelComplement (a b : ℝ) (r : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![a-r 0,b-r 1]

noncomputable def minusKernelBox (p q : Fin 5 → ℝ) (t0 r s t : ℝ) : ℝ :=
  boxIntegral r s t (fun x y z =>
    evalDegreeFour p (x+y+z-t0)*evalDegreeFour q (x+y+z+t0))

noncomputable def minusKernelUniform (p q : Fin 5 → ℝ) (t0 r s t : ℝ) : ℝ :=
  r*s*t*uniformBoxExpectation r s t (fun x y z =>
    evalDegreeFour p (x+y+z-t0)*evalDegreeFour q (x+y+z+t0))

noncomputable def denominatorMinusKernel (p q : Fin 5 → ℝ) (a b c d : ℝ) : ℝ :=
  ∫ x, (boundedSimplexSlice a b c d).indicator
    (fun x => minusKernelUniform p q (minusKernelT0 a b c d)
      (a-x 0) (b-x 1) (c-(d-x 0-x 1))) x

noncomputable def denominatorMinusResidualKernel (p q : Fin 5 → ℝ)
    (a b c d : ℝ) : ℝ :=
  ∫ r, (boundedSimplexSlice a b c (minusKernelH a b c d)).indicator
    (fun r => minusKernelBox p q (minusKernelT0 a b c d)
      (r 0) (r 1) (minusKernelH a b c d-r 0-r 1)) r

theorem boxIntegral_zero_first (s t : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    boxIntegral 0 s t f = 0 := by simp [boxIntegral]

theorem boxIntegral_zero_second (r t : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    boxIntegral r 0 t f = 0 := by simp [boxIntegral]

theorem boxIntegral_zero_third (r s : ℝ) (f : ℝ → ℝ → ℝ → ℝ) :
    boxIntegral r s 0 f = 0 := by simp [boxIntegral]

theorem minusKernelUniform_eq_box {r s t : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : 0 ≤ t) (p q : Fin 5 → ℝ) (t0 : ℝ) :
    minusKernelUniform p q t0 r s t = minusKernelBox p q t0 r s t := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp [minusKernelUniform, minusKernelBox, boxIntegral_zero_first]
  rcases eq_or_lt_of_le hs with rfl | hs
  · simp [minusKernelUniform, minusKernelBox, boxIntegral_zero_second]
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [minusKernelUniform, minusKernelBox, boxIntegral_zero_third]
  unfold minusKernelUniform minusKernelBox
  rw [uniformBoxExpectation_eq_box hr hs ht]
  field_simp

theorem minusKernelComplement_slice (a b c d : ℝ) (r : Fin 2 → ℝ) :
    minusKernelComplement a b r ∈ boundedSimplexSlice a b c d ↔
      r ∈ boundedSimplexSlice a b c (minusKernelH a b c d) := by
  simp only [minusKernelComplement, boundedSimplexSlice, simplexSlice,
    Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, minusKernelH]
  constructor
  · rintro ⟨⟨h1,h2,h3⟩,h4,h5,h6⟩
    repeat' constructor
    all_goals linarith
  · rintro ⟨⟨h1,h2,h3⟩,h4,h5,h6⟩
    repeat' constructor
    all_goals linarith

theorem minusKernelComplement_residuals (a b c d : ℝ) (r : Fin 2 → ℝ) :
    a-(minusKernelComplement a b r) 0 = r 0 ∧
    b-(minusKernelComplement a b r) 1 = r 1 ∧
    c-(d-(minusKernelComplement a b r) 0-(minusKernelComplement a b r) 1) =
      minusKernelH a b c d-r 0-r 1 := by
  simp only [minusKernelComplement, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, minusKernelH]
  repeat' constructor
  all_goals ring

theorem denominatorMinusKernel_eq_residual (p q : Fin 5 → ℝ) (a b c d : ℝ) :
    denominatorMinusKernel p q a b c d = denominatorMinusResidualKernel p q a b c d := by
  classical
  let f := (boundedSimplexSlice a b c d).indicator
    (fun x => minusKernelUniform p q (minusKernelT0 a b c d)
      (a-x 0) (b-x 1) (c-(d-x 0-x 1)))
  change (∫ x, f x) = _
  rw [← integral_sub_left_eq_self f volume (![a,b] : Fin 2 → ℝ)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro r
  have hv : (![a,b] : Fin 2 → ℝ)-r = minusKernelComplement a b r := by
    funext i
    fin_cases i <;> simp [minusKernelComplement]
  change f ((![a,b] : Fin 2 → ℝ)-r) = _
  rw [hv]
  change (boundedSimplexSlice a b c d).indicator
    (fun x => minusKernelUniform p q (minusKernelT0 a b c d)
      (a-x 0) (b-x 1) (c-(d-x 0-x 1))) (minusKernelComplement a b r) = _
  by_cases hr : r ∈ boundedSimplexSlice a b c (minusKernelH a b c d)
  · rw [Set.indicator_of_mem ((minusKernelComplement_slice a b c d r).mpr hr),
      Set.indicator_of_mem hr]
    rcases minusKernelComplement_residuals a b c d r with ⟨h1,h2,h3⟩
    rw [h1,h2,h3]
    exact minusKernelUniform_eq_box hr.1.1 hr.1.2.1 hr.1.2.2 p q _
  · rw [Set.indicator_of_notMem (fun h => hr ((minusKernelComplement_slice a b c d r).mp h)),
      Set.indicator_of_notMem hr]

theorem boundedSimplexSlice_integral_zero_of_nonpos (a b c : ℝ) {H : ℝ}
    (hH : H ≤ 0) (f : (Fin 2 → ℝ) → ℝ) :
    (∫ r, (boundedSimplexSlice a b c H).indicator f r) = 0 := by
  have hn : volume (simplexSlice H) = 0 := by
    rcases lt_or_eq_of_le hH with h | h
    · rw [simplexSlice_empty_of_neg h, measure_empty]
    · rw [h, simplexSlice_zero, measure_singleton]
  have hb : volume (boundedSimplexSlice a b c H) = 0 := by
    apply measure_mono_null (fun _ h => h.1) hn
  apply integral_eq_zero_of_ae
  filter_upwards [compl_mem_ae_iff.mpr hb] with r hr
  exact Set.indicator_of_notMem hr f

theorem denominatorMinusKernel_zero_of_nonpos (p q : Fin 5 → ℝ) (a b c d : ℝ)
    (hH : a+b+c ≤ d) : denominatorMinusKernel p q a b c d = 0 := by
  rw [denominatorMinusKernel_eq_residual]
  unfold denominatorMinusResidualKernel
  exact boundedSimplexSlice_integral_zero_of_nonpos a b c (by
    unfold minusKernelH
    linarith) _

end SixthMoment
