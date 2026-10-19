import Sechstmoment.Numerator.U.ZeroModes.Ratio.PhysicalResidual

/-! A genuine fixed-shift physical residual majorant, independent of
T or of the time profile, for exact front reconstruction. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeRatioPhysicalResidual_growth_bound
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) :
    ∃ C : ℝ,0≤C ∧ ∀ g a b : ℕ,0<g → 0<a → 0<b → ∀ A B : ℕ→ℂ,
      ∀ x : ℝ,0<x → ∀ s : ℂ,1+ε≤s.re →
      ‖a03ZeroModeRatioPhysicalResidual ε α g a b A B x s‖≤
        C*‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖*(a:ℝ)^δ*(b:ℝ)^δ*
          ((x/(g*a:ℕ))^(a03ZeroModeRatioPrimaryLine ε)*(x/(g*b:ℕ))^(a03ZeroModeRatioPrimaryLine ε)+
           (x/(g*b:ℕ))^(a03ZeroModeRatioSecondaryLine ε)+(x/(g*a:ℕ))^(a03ZeroModeRatioSecondaryLine ε)) := by
  obtain ⟨D,hD,hDouble⟩ := a03ZeroModeRatioWeightedKernel_double_residual_norm_bound hε hε1 hδ
  obtain ⟨E,hE,hLeft⟩ := a03ZeroModeRatioWeightedLeftResidue_norm_bound hε hε1 hδ
  obtain ⟨F,hF,hRight⟩ := a03ZeroModeRatioWeightedRightResidue_norm_bound hε hε1 hδ
  let B0 := a03ZeroModeRatioGaussianConstant α 1
  have hB0 : 0≤B0 := a03ZeroModeRatioGaussianConstant_nonneg α 1
  let D0 := D*B0^2
  let E0 := E*‖riemannZeta (1+α 0-α 1)‖*B0
  let F0 := F*‖riemannZeta (1+α 2-α 3)‖*B0
  let C := D0+E0+F0
  have hD0 : 0≤D0 := by dsimp [D0]; positivity
  have hE0 : 0≤E0 := by dsimp [E0]; positivity
  have hF0 : 0≤F0 := by dsimp [F0]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have hDC : D0≤C := by dsimp [C]; linarith
  have hEC : E0≤C := by dsimp [C]; linarith
  have hFC : F0≤C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro g a b hg ha hb A B x hx s hs
  let L := a03ZeroModeRatioPhysicalLogLeft g a x
  let M := a03ZeroModeRatioPhysicalLogRight g b x
  have hd := hDouble L M α hα hρ a b ha.ne' hb.ne' s hs
  have hl := hLeft L M α hα hρ a b ha.ne' hb.ne' s hs
  have hr := hRight L M α hα hρ a b ha.ne' hb.ne' s hs
  have hsum : ‖a03ZeroModeRatioResidual L M ε α a b s‖≤
      C*(a:ℝ)^δ*(b:ℝ)^δ*(Real.exp ((L+M)*a03ZeroModeRatioPrimaryLine ε)+
        Real.exp (M*a03ZeroModeRatioSecondaryLine ε)+Real.exp (L*a03ZeroModeRatioSecondaryLine ε)) := by
    unfold a03ZeroModeRatioResidual
    apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))).trans
    apply (add_le_add (add_le_add hd hl) hr).trans
    change D0*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp ((L+M)*a03ZeroModeRatioPrimaryLine ε)+
      E0*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp (M*a03ZeroModeRatioSecondaryLine ε)+
      F0*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp (L*a03ZeroModeRatioSecondaryLine ε)≤_
    calc
      _≤C*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp ((L+M)*a03ZeroModeRatioPrimaryLine ε)+
        C*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp (M*a03ZeroModeRatioSecondaryLine ε)+
        C*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp (L*a03ZeroModeRatioSecondaryLine ε) := by gcongr
      _=_ := by ring
  rw [a03ZeroModeRatioPhysicalLogPair_exp hg ha hb hx,
    a03ZeroModeRatioPhysicalLogRight_exp hg hb hx,a03ZeroModeRatioPhysicalLogLeft_exp hg ha hx] at hsum
  unfold a03ZeroModeRatioPhysicalResidual
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left hsum (norm_nonneg _)).trans_eq (by ring)

end
end Sechstmoment.Source
