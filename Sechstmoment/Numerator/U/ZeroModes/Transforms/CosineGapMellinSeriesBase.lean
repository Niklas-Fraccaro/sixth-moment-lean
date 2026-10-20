import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Sechstmoment.Numerator.U.ZeroModes.Transforms.SmoothedCosineMellinInversion

namespace Sechstmoment
open Complex Real Set Filter MeasureTheory Source
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem a03GapPower_summable {c : ℝ} (hc : 1<c) :
    Summable (fun h : ℕ => ((h:ℝ)+1)^(-c)) := by
  have hs := (Real.summable_one_div_nat_add_rpow 1 c).mpr hc
  apply hs.congr
  intro h
  rw [abs_of_pos (by positivity),Real.rpow_neg (by positivity),one_div]

theorem a03GapPower_line_norm (c v : ℝ) (h : ℕ) :
    ‖(((h:ℝ)+1:ℝ):ℂ)^(-((c:ℂ)+(v:ℂ)*I))‖=((h:ℝ)+1)^(-c) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  simp

theorem a03GapPower_line_continuous (c : ℝ) (h : ℕ) :
    Continuous (fun v : ℝ => (((h:ℝ)+1:ℝ):ℂ)^(-((c:ℂ)+(v:ℂ)*I))) := by
  have hn : (((h:ℝ)+1:ℝ):ℂ)≠0 := by exact_mod_cast (ne_of_gt (show (0:ℝ)<(h:ℝ)+1 by positivity))
  simp_rw [Complex.cpow_def_of_ne_zero hn]
  fun_prop

theorem a03GapPower_integral_norm {c : ℝ} {K : ℝ→ℂ} (_hK : Integrable K) (h : ℕ) :
    (∫ v : ℝ,‖(((h:ℝ)+1:ℝ):ℂ)^(-((c:ℂ)+(v:ℂ)*I))*K v‖)=
      ((h:ℝ)+1)^(-c)*(∫ v : ℝ,‖K v‖) := by
  simp_rw [norm_mul,a03GapPower_line_norm]
  exact integral_const_mul _ _

theorem a03GapPower_line_integrable {c : ℝ} {K : ℝ→ℂ} (hK : Integrable K) (h : ℕ) :
    Integrable (fun v : ℝ => (((h:ℝ)+1:ℝ):ℂ)^(-((c:ℂ)+(v:ℂ)*I))*K v) := by
  apply (hK.norm.const_mul (((h:ℝ)+1)^(-c))).mono'
    ((a03GapPower_line_continuous c h).aestronglyMeasurable.mul hK.1)
  exact ae_of_all _ (fun v => by dsimp only [Pi.mul_apply]; rw [norm_mul,a03GapPower_line_norm])

theorem a03GapPower_integral_tsum {c : ℝ} (hc : 1<c) {K : ℝ→ℂ} (hK : Integrable K) :
    (∑' h : ℕ, ∫ v : ℝ,(((h:ℝ)+1:ℝ):ℂ)^(-((c:ℂ)+(v:ℂ)*I))*K v)=
      ∫ v : ℝ,riemannZeta ((c:ℂ)+(v:ℂ)*I)*K v := by
  have hS : Summable (fun h : ℕ => ∫ v : ℝ,
      ‖(((h:ℝ)+1:ℝ):ℂ)^(-((c:ℂ)+(v:ℂ)*I))*K v‖) := by
    simpa only [a03GapPower_integral_norm hK] using
      (a03GapPower_summable hc).mul_right (∫ v : ℝ,‖K v‖)
  rw [integral_tsum_of_summable_integral_norm (a03GapPower_line_integrable hK) hS]
  apply integral_congr_ae
  apply ae_of_all
  intro v
  dsimp only
  rw [tsum_mul_right]
  congr 1
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hc)]
  apply tsum_congr
  intro h
  rw [Complex.cpow_neg]
  simp only [one_div,Complex.ofReal_add,Complex.ofReal_natCast,
    Complex.ofReal_one]

end
end Sechstmoment
