import Sechstmoment.Analysis.Integration.ExponentialDifference
import Sechstmoment.Arithmetic.QuadraticDivisor.OrientedInput
import Sechstmoment.Numerator.U.MainTerm.DoubleVerticalCoupling
import Sechstmoment.Numerator.U.MainTerm.PositiveConvolution
import Sechstmoment.Numerator.U.MainTerm.ProfileRationalInversion
import Sechstmoment.Numerator.V.DP.Input
import Sechstmoment.Zeta.Moments.SixTerms
import Sechstmoment.Zeta.Regularized

/-! Actual inverse transform of all five profile-dependent rational factors.
Both vertical profile integrals and the common positive translation variable
are retained, with absolute Fubini supplied by an exponential product bound. -/

namespace Sechstmoment
open Complex Real MeasureTheory Set Source
open scoped BigOperators ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def principalPurePolarProduct (α : MomentShifts) : ℂ :=
  ∏ i : Fin 2, ∏ j : Fin 2, (α ⟨i.val, by omega⟩+α ⟨j.val+2, by omega⟩)

theorem ninePolarRationalFactor_zero_split (α : MomentShifts) (u v : ℂ) :
    ninePolarRationalFactor u v 0 α =
      1 / ((u+v)*(u+α 2)*(u+α 3)*(v+α 0)*(v+α 1)*
        principalPurePolarProduct α) := by
  simp only [ninePolarRationalFactor, ninePolarArgument, polarLeftArguments,
    polarRightArguments, Fintype.prod_prod_type, Fin.prod_univ_succ,
    Fin.prod_univ_zero, principalPurePolarProduct, Matrix.cons_val_zero,
    Matrix.cons_val_succ, zero_add, mul_one]
  simp only [one_div, mul_inv_rev]
  norm_num
  ring

theorem doubleProfileRationalIntegral_eq_positiveConvolution
    {f g : ℝ → ℂ} (hf : HasCompactSupport f) (hfs : ContDiff ℝ ∞ f)
    (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {c : ℝ} (hc : 0 < c) (A B C D : ℂ)
    (hA : 0 < c+A.re) (hB : 0 < c+B.re)
    (hC : 0 < c+C.re) (hD : 0 < c+D.re) (hAB : A ≠ B) (hCD : C ≠ D) :
    (1/(2*π):ℂ)^2 *
      (∫ y : ℝ × ℝ,
        profileLaplaceTransform f (a04VerticalPoint c y.1)*
        profileLaplaceTransform g (a04VerticalPoint c y.2)/
          ((a04VerticalPoint c y.1+a04VerticalPoint c y.2)*
           (a04VerticalPoint c y.1+A)*(a04VerticalPoint c y.1+B)*
           (a04VerticalPoint c y.2+C)*(a04VerticalPoint c y.2+D))
        ∂(volume.prod volume)) =
      ∫ t in Ici (0:ℝ), ∫ x in Ici (0:ℝ), ∫ y in Ici (0:ℝ),
        f (x+t)*g (y+t)*exponentialDifference A B x*exponentialDifference C D y := by
  let F : ℝ → ℂ := fun y => profileLaplaceTransform f (a04VerticalPoint c y)/
    ((a04VerticalPoint c y+A)*(a04VerticalPoint c y+B))
  let G : ℝ → ℂ := fun y => profileLaplaceTransform g (a04VerticalPoint c y)/
    ((a04VerticalPoint c y+C)*(a04VerticalPoint c y+D))
  have hF : Integrable F := profileLaplaceTransform_twoPole_integrable hf hfs c A B hA hB
  have hG : Integrable G := profileLaplaceTransform_twoPole_integrable hg hgs c C D hC hD
  have hFc : Continuous F := profileLaplaceTransform_twoPole_continuous hf hfs.continuous c A B hA hB
  have hGc : Continuous G := profileLaplaceTransform_twoPole_continuous hg hgs.continuous c C D hC hD
  have hcouple := a04DoubleVerticalCoupling hc F G hFc hGc hF hG
  have hp (y : ℝ × ℝ) :
      profileLaplaceTransform f (a04VerticalPoint c y.1)*
      profileLaplaceTransform g (a04VerticalPoint c y.2)/
        ((a04VerticalPoint c y.1+a04VerticalPoint c y.2)*
         (a04VerticalPoint c y.1+A)*(a04VerticalPoint c y.1+B)*
         (a04VerticalPoint c y.2+C)*(a04VerticalPoint c y.2+D)) =
      F y.1*G y.2/(a04VerticalPoint c y.1+a04VerticalPoint c y.2) := by
    dsimp [F,G]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [hp]
  rw [hcouple, ← integral_const_mul, ← integral_Ici_eq_integral_Ioi]
  apply integral_congr_ae
  filter_upwards [] with t
  have hfi := profileLaplaceTransform_shifted_twoPole_inversion hf hfs c t A B hA hB hAB
  have hgi := profileLaplaceTransform_shifted_twoPole_inversion hg hgs c t C D hC hD hCD
  have heF : (∫ y : ℝ, F y*Complex.exp (-a04VerticalPoint c y*t)) =
      ∫ y : ℝ, profileLaplaceTransform f ((c:ℂ)+(y:ℂ)*I)*
        Complex.exp (-((c:ℂ)+(y:ℂ)*I)*t)/
          (((c:ℂ)+(y:ℂ)*I+A)*((c:ℂ)+(y:ℂ)*I+B)) := by
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [F,a04VerticalPoint]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have heG : (∫ y : ℝ, G y*Complex.exp (-a04VerticalPoint c y*t)) =
      ∫ y : ℝ, profileLaplaceTransform g ((c:ℂ)+(y:ℂ)*I)*
        Complex.exp (-((c:ℂ)+(y:ℂ)*I)*t)/
          (((c:ℂ)+(y:ℂ)*I+C)*((c:ℂ)+(y:ℂ)*I+D)) := by
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp [G,a04VerticalPoint]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heF,heG]
  calc
    _ = ((1/(2*π):ℂ)*∫ y : ℝ, profileLaplaceTransform f ((c:ℂ)+(y:ℂ)*I)*
          Complex.exp (-((c:ℂ)+(y:ℂ)*I)*t)/
          (((c:ℂ)+(y:ℂ)*I+A)*((c:ℂ)+(y:ℂ)*I+B))) *
        ((1/(2*π):ℂ)*∫ y : ℝ, profileLaplaceTransform g ((c:ℂ)+(y:ℂ)*I)*
          Complex.exp (-((c:ℂ)+(y:ℂ)*I)*t)/
          (((c:ℂ)+(y:ℂ)*I+C)*((c:ℂ)+(y:ℂ)*I+D))) := by ring
    _ = _ := by
      rw [hfi,hgi]
      simp only [← integral_Ici_eq_integral_Ioi]
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      unfold exponentialDifference
      ring

end
end Sechstmoment
