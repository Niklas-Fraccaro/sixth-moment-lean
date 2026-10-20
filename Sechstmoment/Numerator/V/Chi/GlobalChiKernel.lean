import Sechstmoment.Numerator.V.Chi.KernelBounds
import Sechstmoment.Numerator.V.Chi.WeightedKernelScaling
import Sechstmoment.Numerator.V.Contour.ShiftedLineGeometry


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped FourierTransform
noncomputable section

theorem noDPChiTimeTransform_global_weighted_error (h : SchwartzMap ℝ ℂ)
    (hs : tsupport (𝓕⁻ (h:ℝ → ℂ)) ⊆ Icc (1:ℝ) 2) (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 3 (100*Real.pi) ≤ T →
      ∀ c ∈ Icc (1:ℝ) (15/8), c ≤ 1+A/Real.log T → ∀ r : ℝ, 0 < r →
      ‖noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T c 0 r-
        Complex.exp (I*((-2*Real.pi*r:ℝ):ℂ))*𝓕⁻ (h:ℝ → ℂ) (2*Real.pi*r/T)‖ ≤
        C*r^(-c)*T^(1/2:ℝ) := by
  obtain ⟨D,hD,hmain⟩ := noDPChiTimeTransform_main_error h hs
  obtain ⟨E,hE,hfar⟩ := noDPChiTimeTransform_far_bound h hs
  let B := Real.exp ((5/4:ℝ)*A)
  have hB : 0 < B := Real.exp_pos _
  let C := (D+E)*(1+2*B)
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro T hT c hc hcline r hr
  have hT3 : 3 ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  have hc0 : 0 ≤ c := by linarith [hc.1]
  have hbase : r^c*r^(-c) = 1 := by rw [← Real.rpow_add hr]; simp
  have hsmall : 1/T^2 ≤ T^(1/2:ℝ) := by
    have hden : 1 ≤ T^2 := one_le_pow₀ hT1.le
    have hp : 1 ≤ T^(1/2:ℝ) := by
      simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hT1.le
        (by norm_num : (0:ℝ) ≤ 1/2)
    exact ((div_le_one (pow_pos hT0 2)).mpr hden).trans hp
  have hnormalize (Q v : ℝ) :
      r^c*(Q*(r^(-c)/T^2+v)) = Q*(1/T^2+r^c*v) := by
    calc
      _ = Q*((r^c*r^(-c))/T^2+r^c*v) := by ring
      _ = _ := by rw [hbase]
  have hweighted : r^c*‖noDPChiTimeTransform (𝓕⁻ (h:ℝ → ℂ)) T c 0 r-
      Complex.exp (I*((-2*Real.pi*r:ℝ):ℂ))*𝓕⁻ (h:ℝ → ℂ) (2*Real.pi*r/T)‖ ≤
      C*T^(1/2:ℝ) := by
    by_cases hnear : r ≤ T^(5/4:ℝ)
    · have Hmain := hmain T hT c hc r hr
      have Hbudget := logarithmic_line_near_kernel_budget hT1 hc0 hcline hr hnear
      have H := mul_le_mul_of_nonneg_left Hmain (Real.rpow_nonneg hr.le c)
      have he : r^(-c)/T^2+1/T+r/T^2 = r^(-c)/T^2+(1/T+r/T^2) := by ring
      rw [he,hnormalize] at H
      apply H.trans
      calc
        _ ≤ D*(T^(1/2:ℝ)+2*B*T^(1/2:ℝ)) := by gcongr
        _ = D*(1+2*B)*T^(1/2:ℝ) := by ring
        _ ≤ C*T^(1/2:ℝ) := by dsimp only [C]; gcongr; linarith
    · have hXr : T^(5/4:ℝ) ≤ r := le_of_lt (lt_of_not_ge hnear)
      have hTr : T ≤ r := by
        have H : T ≤ T^(5/4:ℝ) := by
          simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1.le
            (by norm_num : (1:ℝ) ≤ 5/4)
        exact H.trans hXr
      have hpoint : 2*Real.pi ≤ 2*Real.pi*r/T :=
        (le_div_iff₀ hT0).mpr (mul_le_mul_of_nonneg_left hTr (by positivity))
      have hzero : 𝓕⁻ (h:ℝ → ℂ) (2*Real.pi*r/T) = 0 := by
        apply Function.notMem_support.mp
        intro hm
        have Hsupp := hs (subset_tsupport _ hm)
        linarith [Hsupp.2,Real.two_le_pi]
      rw [hzero,mul_zero,sub_zero]
      have Hfar := hfar T hT c hc r hr
      have Hbudget := logarithmic_line_far_kernel_budget hT1 (by linarith [hc.2]) hcline hXr
      have H := mul_le_mul_of_nonneg_left Hfar (Real.rpow_nonneg hr.le c)
      rw [hnormalize] at H
      apply H.trans
      calc
        _ ≤ E*(T^(1/2:ℝ)+B*T^(1/2:ℝ)) := by gcongr
        _ ≤ E*(T^(1/2:ℝ)+2*B*T^(1/2:ℝ)) := by gcongr; linarith
        _ = E*(1+2*B)*T^(1/2:ℝ) := by ring
        _ ≤ C*T^(1/2:ℝ) := by dsimp only [C]; gcongr; linarith
  apply (mul_le_mul_iff_of_pos_left (Real.rpow_pos_of_pos hr c)).mp
  apply hweighted.trans_eq
  calc
    _ = C*(r^c*r^(-c))*T^(1/2:ℝ) := by rw [hbase,mul_one]
    _ = _ := by ring

end
end Sechstmoment.Source
