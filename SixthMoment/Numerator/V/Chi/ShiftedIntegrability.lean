import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import SixthMoment.Numerator.V.Chi.ShiftedKernel


namespace SixthMoment.Source
open Complex Real Set MeasureTheory
noncomputable section

theorem chi_shift_vertical_identity (c t : ℝ) (u : ℂ) :
    1-((c:ℂ)+(t:ℂ)*I)+u =
      1-(((c-u.re:ℝ):ℂ)+((t-u.im:ℝ):ℂ)*I) := by
  apply Complex.ext <;> simp <;> ring

theorem chi_shift_vertical_aestronglyMeasurable {c : ℝ} {u : ℂ}
    (hc : 0 < c-u.re) :
    AEStronglyMeasurable (fun t : ℝ => zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)) volume := by
  have H := (chi_vertical_aestronglyMeasurable hc).comp_measurePreserving
    (measurePreserving_add_right volume (-u.im))
  convert H using 1
  funext t
  rw [chi_shift_vertical_identity]
  simp only [sub_eq_add_neg,Function.comp_apply]

theorem chi_shift_compact_time_weight_integrable {w : ℝ → ℂ}
    (hw : Continuous w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {T c : ℝ} {u : ℂ} (hT : 1 ≤ T)
    (hc : c-u.re ∈ Icc (1/8:ℝ) (15/8)) (hu : |u.im| ≤ T/2) :
    Integrable (fun t : ℝ => zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)*w (t/T)) := by
  obtain ⟨D,hD,hchi⟩ := chi_positive_strip_global_polynomial_bound
  have hK : HasCompactSupport w :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hws
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuous hw
  let M := D*(1+3*T)^2*max B 0
  have hT0 : 0 < T := by linarith
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  let S := Icc T (2*T)
  have hi : Integrable (S.indicator (fun _ : ℝ => M)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((continuous_const : Continuous (fun _ : ℝ => M)).continuousOn.integrableOn_Icc)
  have hwT : Continuous (fun t : ℝ => w (t/T)) := hw.comp (by fun_prop)
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)*w (t/T)) volume :=
    (chi_shift_vertical_aestronglyMeasurable
      (by linarith [hc.1] : 0 < c-u.re)).mul
      hwT.aestronglyMeasurable
  apply hi.mono' hmeas
  filter_upwards [volume.ae_ne u.im] with t htne
  by_cases ht : t ∈ S
  · rw [Set.indicator_of_mem ht,norm_mul,chi_shift_vertical_identity]
    have hdiff : |t-u.im| ≤ 3*T := by
      have H := abs_le.mp hu
      exact abs_le.mpr ⟨by linarith [ht.1,H.2],by linarith [ht.2,H.1]⟩
    have H := hchi (c-u.re) hc (t-u.im) (sub_ne_zero.mpr htne)
    calc
      _ ≤ (D*(1+|t-u.im|)^2)*max B 0 :=
        mul_le_mul H ((hB _).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
      _ ≤ M := by dsimp only [M]; gcongr
  · have hz : w (t/T) = 0 := by
      apply Function.notMem_support.mp
      intro hm
      have H := hws (subset_tsupport w hm)
      exact ht ⟨by simpa using (le_div_iff₀ hT0).mp H.1,(div_le_iff₀ hT0).mp H.2⟩
    simp only [hz,mul_zero,norm_zero,Set.indicator_of_notMem ht]
    exact le_rfl

end
end SixthMoment.Source
