import Sechstmoment.Numerator.U.ZeroModes.VStarMellin

/-! Genuine weighted absolute x-masses of VStar and their real scaling law. -/
namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 500000

def a03VStarAbsoluteSquareMass (G : ℂ→ℂ) (r Y : ℝ) : ℝ :=
  ∫x : ℝ in Ioi 0,x^(r-1)*‖bblrVStar G (x^2/Y^2)‖

theorem a03VStarAbsoluteSquareMass_integrable {r Y : ℝ} (hr : 0<r) (hY : 0<Y)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    IntegrableOn (fun x : ℝ => x^(r-1)*‖bblrVStar G (x^2/Y^2)‖) (Ioi 0) := by
  have hi0 : IntegrableOn (fun x : ℝ => (x:ℂ)^((r:ℂ)-1)*bblrVStar G (x^2/Y^2)) (Ioi 0) := by
    exact (bblrVStar_square_scaled_xMellin (q:=(r:ℂ)) (by simpa using hr) hY G α hG).1
  have hi : IntegrableOn (fun x : ℝ => ‖(x:ℂ)^((r:ℂ)-1)*bblrVStar G (x^2/Y^2)‖) (Ioi 0) := hi0.norm
  apply hi.congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,
    Complex.sub_re,Complex.ofReal_re,Complex.one_re]

theorem a03VStarAbsoluteSquareMass_nonneg (G : ℂ→ℂ) (r Y : ℝ) :
    0≤a03VStarAbsoluteSquareMass G r Y := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro x hx
  exact mul_nonneg (Real.rpow_nonneg hx.le _) (norm_nonneg _)

theorem a03VStarAbsoluteSquareMass_scale (G : ℂ→ℂ) (r : ℝ) {Y : ℝ} (hY : 0<Y) :
    a03VStarAbsoluteSquareMass G r Y=Y^r*a03VStarAbsoluteSquareMass G r 1 := by
  let f : ℝ→ℝ := fun x => x^(r-1)*‖bblrVStar G (x^2)‖
  have he (x : ℝ) (hx : x∈Ioi (0:ℝ)) :
      x^(r-1)*‖bblrVStar G (x^2/Y^2)‖=Y^(r-1)*f (Y⁻¹*x) := by
    have hxy : Y*(Y⁻¹*x)=x := by field_simp
    have hp : (Y*(Y⁻¹*x))^(r-1)=Y^(r-1)*(Y⁻¹*x)^(r-1) :=
      Real.mul_rpow hY.le (mul_nonneg (inv_pos.mpr hY).le hx.le)
    rw [hxy] at hp
    rw [hp,show x^2/Y^2=(Y⁻¹*x)^2 by ring]
    dsimp only [f]
    ring
  unfold a03VStarAbsoluteSquareMass
  rw [setIntegral_congr_fun measurableSet_Ioi he,integral_const_mul,
    integral_comp_mul_left_Ioi f 0 (inv_pos.mpr hY)]
  simp only [inv_inv,mul_zero,smul_eq_mul,one_pow,div_one]
  have hp : Y^(r-1)*Y=Y^r := by
    calc
      _=Y^(r-1)*Y^(1:ℝ) := by rw [Real.rpow_one]
      _=Y^((r-1)+1) := (Real.rpow_add hY _ _).symm
      _=Y^r := by congr 1; ring
  dsimp only [f]
  rw [←mul_assoc,hp]

end
end Sechstmoment.Source
