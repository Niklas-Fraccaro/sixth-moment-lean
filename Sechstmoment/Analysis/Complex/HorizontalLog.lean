import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! A branch-safe quantitative logarithm comparison on every horizontal line
off the real axis. Used to simplify the two Gamma powers in the chi phase. -/

namespace Sechstmoment.Source
open Complex Real Set
noncomputable section

theorem norm_log_horizontal_sub (a b : ℝ) (hb : b ≠ 0) :
    ‖Complex.log ((a:ℂ)+(b:ℂ)*I)-Complex.log ((b:ℂ)*I)‖ ≤ |a|/|b| := by
  let f := fun x : ℝ => Complex.log ((x:ℂ)+(b:ℂ)*I)
  have hslit (x : ℝ) : (x:ℂ)+(b:ℂ)*I ∈ Complex.slitPlane := by
    simp [Complex.mem_slitPlane_iff,hb]
  have hd (x : ℝ) : HasDerivAt f (((x:ℂ)+(b:ℂ)*I)⁻¹) x := by
    have ho : HasDerivAt (fun y : ℝ => (y:ℂ)) (1:ℂ) x := by
      simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using!
        (Complex.ofRealCLM.hasDerivAt (x := x))
    simpa only [one_div] using (ho.add_const ((b:ℂ)*I)).clog_real (hslit x)
  have hbound (x : ℝ) : ‖((x:ℂ)+(b:ℂ)*I)⁻¹‖ ≤ (|b|)⁻¹ := by
    have hm := Complex.abs_im_le_norm ((x:ℂ)+(b:ℂ)*I)
    simp only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add] at hm
    rw [norm_inv]
    simpa only [one_div] using one_div_le_one_div_of_le (abs_pos.mpr hb) hm
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (Set.univ : Set ℝ)) => (hd x).hasDerivWithinAt)
    (fun x (_ : x ∈ (Set.univ : Set ℝ)) => hbound x)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (Set.mem_univ (0:ℝ)) (Set.mem_univ a)
  simpa only [f,Complex.ofReal_zero,zero_add,sub_zero,Real.norm_eq_abs,
    div_eq_mul_inv,mul_comm] using H

end
end Sechstmoment.Source
