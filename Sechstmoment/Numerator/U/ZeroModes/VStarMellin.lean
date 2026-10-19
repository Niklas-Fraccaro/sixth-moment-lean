import Sechstmoment.Numerator.U.ZeroModes.ForwardMellin
import Sechstmoment.Numerator.U.ZeroModes.PolarChamberInvariance

/-! Exact x-Mellin evaluation of the actual gamma-free V* factor used in
BBLR §2.4. Absolute convergence is a conclusion on the positive Mellin strip. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

theorem bblrVStar_square_scaled_forwardMellin {q : ℂ} (hq : 0<q.re)
    {Y : ℝ} (hY : 0<Y) (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) :
    mellin (fun x : ℝ => bblrVStar G (x^2/Y^2)) q=
      (Y:ℂ)^q*(2*Real.pi:ℂ)^(-q)*(G (q/2)/q) := by
  have hq2 : 0<(q/2).re := by simp only [Complex.div_ofNat_re]; linarith
  have hshape : (fun x : ℝ => bblrVStar G (x^2/Y^2))=
      (fun x : ℝ => (fun u : ℝ => bblrVStar G (u^(2:ℝ))) (Y⁻¹*x)) := by
    funext x
    dsimp only
    rw [Real.rpow_two]
    congr 1
    ring
  rw [hshape]
  rw [mellin_comp_mul_left (fun u : ℝ => bblrVStar G (u^(2:ℝ))) q (inv_pos.mpr hY),
    mellin_comp_rpow]
  simp only [Complex.ofReal_ofNat]
  rw [bblrVStar_forwardMellin hq2 G α hG]
  simp only [abs_of_pos (by norm_num : 0<(2:ℝ)),Complex.real_smul,smul_eq_mul]
  have hscale : (Y⁻¹:ℂ)^(-q)=(Y:ℂ)^q := by
    rw [Complex.inv_cpow_ofReal_nonneg hY.le,Complex.cpow_neg,inv_inv]
  have hscale' : ((Y⁻¹:ℝ):ℂ)^(-q)=(Y:ℂ)^q := by simpa only [Complex.ofReal_inv] using hscale
  rw [hscale']
  have harg : -2*(q/2)=-q := by ring
  rw [harg]
  push_cast
  ring

theorem bblrVStar_square_scaled_mellinConvergent {q : ℂ} (hq : 0<q.re)
    {Y : ℝ} (hY : 0<Y) (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) :
    MellinConvergent (fun x : ℝ => bblrVStar G (x^2/Y^2)) q := by
  have hq2 : 0<(q/2).re := by simp only [Complex.div_ofNat_re]; linarith
  have hi := (MellinConvergent.comp_rpow (by norm_num : (2:ℝ)≠0)).mpr
    (bblrVStar_mellinConvergent hq2 G α hG)
  have hs := (MellinConvergent.comp_mul_left (inv_pos.mpr hY)).mpr hi
  apply hs.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x _hx
  simp only [smul_eq_mul,Real.rpow_two]
  congr 2
  ring

/-- The literal x integral from BBLR §2.4, before the arithmetic and
functional-equation substitutions. -/
theorem bblrVStar_square_scaled_xMellin {q : ℂ} (hq : 0<q.re)
    {Y : ℝ} (hY : 0<Y) (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(q-1)*bblrVStar G (x^2/Y^2)) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0,(x:ℂ)^(q-1)*bblrVStar G (x^2/Y^2))=
      (Y:ℂ)^q*(2*Real.pi:ℂ)^(-q)*(G (q/2)/q) :=
  ⟨bblrVStar_square_scaled_mellinConvergent hq hY G α hG,
    bblrVStar_square_scaled_forwardMellin hq hY G α hG⟩

/-- The actual polar weight supplies every Mellin regularity hypothesis. -/
theorem a03GaussianVStar_square_scaled_xMellin {q : ℂ} (hq : 0<q.re)
    {Y : ℝ} (hY : 0<Y) (T : ℝ) (σ : MomentShifts) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(q-1)*bblrVStar (polarPoleKiller T σ) (x^2/Y^2)) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0,(x:ℂ)^(q-1)*bblrVStar (polarPoleKiller T σ) (x^2/Y^2))=
      (Y:ℂ)^q*(2*Real.pi:ℂ)^(-q)*(polarPoleKiller T σ (q/2)/q) :=
  bblrVStar_square_scaled_xMellin hq hY _ (rawMomentShifts T σ)
    (polarPoleKiller_BBLREntireWeight T σ _)

end
end Sechstmoment.Source
