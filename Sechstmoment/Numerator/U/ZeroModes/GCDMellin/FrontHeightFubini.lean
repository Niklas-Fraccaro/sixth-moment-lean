import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.FrontFubini

/-! The outer s-height of the actual eta front is integrable as a consequence
of its genuine s/x/u/v product integrability. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeGCDEtaFrontBlock_height_integrable_of_joint
    (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts) (g a b : ℕ) (A B : ℕ→ℂ)
    (cu cv cs : ℝ)
    (hJoint : Integrable (fun p : ℝ×(ℝ×(ℝ×ℝ)) =>
      a03ZeroModeGCDInitialDensity Φ T σ α g a b A B p.2.1
        ((cu:ℂ)+(p.2.2.1:ℂ)*I) ((cv:ℂ)+(p.2.2.2:ℂ)*I) ((cs:ℂ)+(p.1:ℂ)*I))
      (volume.prod ((volume.restrict (Ioi 0)).prod (volume.prod volume)))) :
    Integrable (fun y : ℝ => a03ZeroModeRatioDoubleIntegral cu cv
      (fun u v => a03ZeroModeGCDEtaFrontBlock Φ T σ α g a b A B u v ((cs:ℂ)+(y:ℂ)*I))) := by
  apply (hJoint.integral_prod_left.const_mul ((1/(2*Real.pi):ℂ)^2)).congr
  filter_upwards [hJoint.prod_right_ae] with y hy
  have hAfter : Integrable (fun p : ℝ×ℝ => a03ZeroModeGCDEtaFrontBlock Φ T σ α g a b A B
      ((cu:ℂ)+(p.1:ℂ)*I) ((cv:ℂ)+(p.2:ℂ)*I) ((cs:ℂ)+(y:ℂ)*I)) (volume.prod volume) := by
    simpa only [a03ZeroModeGCDEtaFrontBlock,a03ZeroModeGCDInitialDensity,Function.comp_def,Prod.swap_prod_mk] using
      hy.swap.integral_prod_left
  rw [a03ZeroModeRatioDoubleIntegral_eq_product cu cv _ hAfter]
  congr 1
  change (∫q : ℝ×(ℝ×ℝ),a03ZeroModeGCDInitialDensity Φ T σ α g a b A B q.1
      ((cu:ℂ)+(q.2.1:ℂ)*I) ((cv:ℂ)+(q.2.2:ℂ)*I) ((cs:ℂ)+(y:ℂ)*I)
      ∂((volume.restrict (Ioi 0)).prod (volume.prod volume)))=
    ∫p : ℝ×ℝ,(∫x : ℝ in Ioi 0,a03ZeroModeGCDInitialDensity Φ T σ α g a b A B x
      ((cu:ℂ)+(p.1:ℂ)*I) ((cv:ℂ)+(p.2:ℂ)*I) ((cs:ℂ)+(y:ℂ)*I)) ∂(volume.prod volume)
  rw [integral_prod _ hy,integral_integral_swap hy]

end
end Sechstmoment.Source
