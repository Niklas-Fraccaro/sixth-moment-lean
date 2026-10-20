import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

open MeasureTheory Set

noncomputable section

namespace Sechstmoment

theorem integral_Ici_comp_add_right (F : ℝ → ℂ) (t : ℝ) :
    (∫ x in Ici 0, F (x + t)) = ∫ x in Ici t, F x := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) t).setIntegral_preimage_emb
    (MeasurableEquiv.addRight t).measurableEmbedding F (Ici t)
  have hs : (fun x : ℝ => x + t) ⁻¹' Ici t = Ici 0 := by
    ext x
    simp only [mem_preimage, mem_Ici]
    constructor <;> intro hx <;> linarith
  simpa only [hs] using h

def positiveConvolutionDomain (a b : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2 ∧
    p.2.1 ∈ Icc 0 a ∧ p.2.2 ∈ Icc 0 b}

private theorem positiveConvolutionDomain_compact (a b : ℝ) :
    IsCompact (positiveConvolutionDomain a b) := by
  have hc : IsClosed (positiveConvolutionDomain a b) := by
    unfold positiveConvolutionDomain
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst (continuous_fst.comp continuous_snd)).inter
      ((isClosed_le continuous_fst (continuous_snd.comp continuous_snd)).inter
      (((isClosed_Icc : IsClosed (Icc (0 : ℝ) a)).preimage
        (continuous_fst.comp continuous_snd)).inter
      ((isClosed_Icc : IsClosed (Icc (0 : ℝ) b)).preimage
        (continuous_snd.comp continuous_snd)))))
  refine ((isCompact_Icc : IsCompact (Icc (0 : ℝ) a)).prod
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) a)).prod
      (isCompact_Icc : IsCompact (Icc (0 : ℝ) b)))).of_isClosed_subset hc ?_
  intro p hp
  exact ⟨⟨hp.1, le_trans hp.2.1 hp.2.2.2.1.2⟩, hp.2.2.2.1, hp.2.2.2.2⟩

def positiveConvolutionIntegrand (f g : ℝ → ℂ) (K : ℝ × ℝ → ℂ)
    (p : ℝ × ℝ × ℝ) : ℂ :=
  if 0 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2 then
    f p.2.1 * g p.2.2 * K (p.2.1 - p.1, p.2.2 - p.1)
  else 0

theorem positiveConvolutionIntegrand_integrable
    (a b : ℝ) (f g : ℝ → ℂ) (K : ℝ × ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hK : Continuous K)
    (hfs : ∀ x ∉ Icc 0 a, f x = 0) (hgs : ∀ y ∉ Icc 0 b, g y = 0) :
    Integrable (positiveConvolutionIntegrand f g K)
      (volume.prod (volume.prod volume)) := by
  let G : ℝ × ℝ × ℝ → ℂ := fun p =>
    f p.2.1 * g p.2.2 * K (p.2.1 - p.1, p.2.2 - p.1)
  have hG : Continuous G := by
    dsimp [G]
    fun_prop
  have heq : positiveConvolutionIntegrand f g K =
      (positiveConvolutionDomain a b).indicator G := by
    funext p
    by_cases hp : 0 ≤ p.1 ∧ p.1 ≤ p.2.1 ∧ p.1 ≤ p.2.2
    · by_cases hfa : p.2.1 ∈ Icc 0 a
      · by_cases hgb : p.2.2 ∈ Icc 0 b
        · rw [indicator_of_mem (show p ∈ positiveConvolutionDomain a b from
            ⟨hp.1, hp.2.1, hp.2.2, hfa, hgb⟩)]
          simp [positiveConvolutionIntegrand, hp, G]
        · rw [indicator_of_notMem (show p ∉ positiveConvolutionDomain a b from
            fun h => hgb h.2.2.2.2)]
          simp [positiveConvolutionIntegrand, hp, hgs _ hgb]
      · rw [indicator_of_notMem (show p ∉ positiveConvolutionDomain a b from
          fun h => hfa h.2.2.2.1)]
        simp [positiveConvolutionIntegrand, hp, hfs _ hfa]
    · rw [indicator_of_notMem (show p ∉ positiveConvolutionDomain a b from
        fun h => hp ⟨h.1,h.2.1,h.2.2.1⟩)]
      simp only [positiveConvolutionIntegrand, hp, ↓reduceIte]
  rw [heq]
  exact (integrable_indicator_iff (positiveConvolutionDomain_compact a b).measurableSet).mpr
    (hG.continuousOn.integrableOn_compact (positiveConvolutionDomain_compact a b))

private theorem positiveConvolution_slice (f g : ℝ → ℂ) (K : ℝ × ℝ → ℂ) (t : ℝ) :
    (∫ A, ∫ B, positiveConvolutionIntegrand f g K (t,A,B)) =
      (Ici 0).indicator (fun t =>
        ∫ A in Ici t, ∫ B in Ici t,
          f A * g B * K (A-t,B-t)) t := by
  by_cases ht : 0 ≤ t
  · rw [indicator_of_mem (show t ∈ Ici 0 from ht)]
    rw [← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards [] with A
    by_cases hA : t ≤ A
    · rw [indicator_of_mem (show A ∈ Ici t from hA), ← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards [] with B
      by_cases hB : t ≤ B <;>
        simp [positiveConvolutionIntegrand, ht, hA, hB]
    · simp [positiveConvolutionIntegrand, ht, hA]
  · simp [positiveConvolutionIntegrand, ht]

private theorem positiveConvolution_double_translate
    (f g : ℝ → ℂ) (K : ℝ × ℝ → ℂ) (t : ℝ) :
    (∫ x in Ici 0, ∫ y in Ici 0, f (x+t) * g (y+t) * K (x,y)) =
      ∫ A in Ici t, ∫ B in Ici t, f A * g B * K (A-t,B-t) := by
  calc
    _ = ∫ x in Ici 0, ∫ B in Ici t, f (x+t) * g B * K (x,B-t) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simpa only [add_sub_cancel_right] using
        integral_Ici_comp_add_right (fun B => f (x+t) * g B * K (x,B-t)) t
    _ = _ := by
      simpa only [add_sub_cancel_right] using integral_Ici_comp_add_right
        (fun A => ∫ B in Ici t, f A * g B * K (A-t,B-t)) t

private theorem positiveConvolution_time_integral
    (f g : ℝ → ℂ) (K : ℝ × ℝ → ℂ) (A B : ℝ) :
    (∫ t, positiveConvolutionIntegrand f g K (t,A,B)) =
      f A * g B * ∫ t in Icc 0 (min A B), K (A-t,B-t) := by
  rw [← integral_const_mul, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with t
  simp [positiveConvolutionIntegrand, indicator, mem_Icc]

theorem positiveConvolution_eq_compact
    (a b : ℝ) (f g : ℝ → ℂ) (K : ℝ × ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hK : Continuous K)
    (hfs : ∀ x ∉ Icc 0 a, f x = 0) (hgs : ∀ y ∉ Icc 0 b, g y = 0) :
    (∫ t in Ici 0, ∫ x in Ici 0, ∫ y in Ici 0,
      f (x+t) * g (y+t) * K (x,y)) =
      ∫ A in Icc 0 a, ∫ B in Icc 0 b,
        f A * g B * ∫ t in Icc 0 (min A B), K (A-t,B-t) := by
  let H := positiveConvolutionIntegrand f g K
  have hH : Integrable H (volume.prod (volume.prod volume)) :=
    positiveConvolutionIntegrand_integrable a b f g K hf hg hK hfs hgs
  calc
    _ = ∫ t in Ici 0, ∫ A in Ici t, ∫ B in Ici t,
          f A * g B * K (A-t,B-t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact positiveConvolution_double_translate f g K t
    _ = ∫ t, ∫ A, ∫ B, H (t,A,B) := by
      simp_rw [H, positiveConvolution_slice]
      rw [integral_indicator measurableSet_Ici]
    _ = ∫ t, ∫ AB, H (t,AB) ∂(volume.prod volume) := by
      apply integral_congr_ae
      filter_upwards [hH.prod_right_ae] with t ht
      exact (integral_prod _ ht).symm
    _ = ∫ AB, ∫ t, H (t,AB) ∂volume ∂(volume.prod volume) :=
      integral_integral_swap hH
    _ = ∫ A, ∫ B, ∫ t, H (t,A,B) :=
      integral_prod _ hH.integral_prod_right
    _ = ∫ A, ∫ B, f A * g B * ∫ t in Icc 0 (min A B), K (A-t,B-t) := by
      simp_rw [H, positiveConvolution_time_integral]
    _ = ∫ A in Icc 0 a, ∫ B,
          f A * g B * ∫ t in Icc 0 (min A B), K (A-t,B-t) := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro A hA
      simp [hfs A hA]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with A
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro B hB
      simp [hgs B hB]

theorem positiveConvolution_eq_interval_compact
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f g : ℝ → ℂ) (K : ℝ × ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (hK : Continuous K)
    (hfs : ∀ x ∉ Icc 0 a, f x = 0) (hgs : ∀ y ∉ Icc 0 b, g y = 0) :
    (∫ t in Ici 0, ∫ x in Ici 0, ∫ y in Ici 0,
      f (x+t) * g (y+t) * K (x,y)) =
      ∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
        f A * g B * ∫ t in (0:ℝ)..min A B, K (A-t,B-t) := by
  rw [positiveConvolution_eq_compact a b f g K hf hg hK hfs hgs]
  rw [intervalIntegral.integral_of_le ha, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro A hA
  dsimp only
  rw [intervalIntegral.integral_of_le hb, ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro B hB
  dsimp only
  rw [intervalIntegral.integral_of_le (le_min hA.1 hB.1),
    ← integral_Icc_eq_integral_Ioc]

end Sechstmoment
