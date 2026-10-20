import Sechstmoment.Numerator.V.Chi.StartingLine


namespace Sechstmoment.Source
open Complex Real Set
noncomputable section

theorem chiTransformMain_wide_log_line_norm_bound {T A c t : ℝ}
    (hT : 64 ≤ T) (hc : 1/2 ≤ c) (hc' : c ≤ 1+A/Real.log T)
    (ht : t ∈ Icc (T/2) (3*T)) :
    ‖chiTransformMain c t‖ ≤ Real.exp A*T^(1/2:ℝ) := by
  have hT1 : 1 < T := by linarith
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith [ht.1]
  have hL : 0 < Real.log T := Real.log_pos hT1
  have hp : 0 < 2*Real.pi := by positivity
  have hb : 0 < t/(2*Real.pi) := div_pos ht0 hp
  have hbT : t/(2*Real.pi) ≤ T := by
    apply (div_le_iff₀ hp).mpr
    have H := mul_le_mul_of_nonneg_right
      (show (3:ℝ) ≤ 2*Real.pi by linarith [Real.two_le_pi]) hT0.le
    linarith [ht.2]
  have hscale : T^(A/Real.log T) = Real.exp A := by
    rw [Real.rpow_def_of_pos hT0]
    congr 1
    field_simp [hL.ne']
  rw [chiTransformMain_norm c ht0]
  calc
    _ ≤ T^(c-1/2) := Real.rpow_le_rpow hb.le hbT (by linarith)
    _ ≤ T^((1/2:ℝ)+A/Real.log T) :=
      Real.rpow_le_rpow_of_exponent_le hT1.le (by linarith)
    _ = _ := by rw [Real.rpow_add hT0,hscale]; ring

theorem chi_transform_wide_log_line_bound {T A c t : ℝ}
    (hT : 64 ≤ T) (hc : c ∈ Icc (1/2:ℝ) 2) (hc' : c ≤ 1+A/Real.log T)
    (ht : t ∈ Icc (T/2) (3*T)) :
    ‖zetaChi (1-((c:ℂ)+(t:ℂ)*I))‖ ≤ 131*Real.exp A*T^(1/2:ℝ) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith [ht.1]
  have hphase := chiTransformMain_wide_log_line_norm_bound hT hc.1 hc' ht
  have herr := chi_transform_main_error (by linarith [hc.1] : 0 < c)
    (by rw [abs_of_nonneg (by linarith [hc.1] : 0 ≤ c)]; exact hc.2)
    (by linarith [ht.1] : 32 ≤ t)
  have hrate : 130/t ≤ 130 := by
    apply (div_le_iff₀ ht0).mpr
    linarith [ht.1]
  have hpos : 0 ≤ Real.exp A*T^(1/2:ℝ) := by positivity
  have herror := herr.trans (mul_le_mul hphase hrate (by positivity) hpos)
  have H := norm_sub_le
    (zetaChi (1-((c:ℂ)+(t:ℂ)*I))-chiTransformMain c t) (-chiTransformMain c t)
  simp only [sub_neg_eq_add,sub_add_cancel,norm_neg] at H
  linarith

end
end Sechstmoment.Source
