import Sechstmoment.Zeta.AFE.Four.DualBound
import Sechstmoment.Zeta.AFE.Two.Gamma

namespace Sechstmoment.Source
open Complex Filter Set
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option maxHeartbeats 2000000

def rawSecondMomentShifts (T : ℝ) (σ : SecondMomentShifts) : SecondMomentShifts :=
  fun j => σ j/(Real.log T:ℂ)

def secondDualMultiplier (t : ℝ) (α : SecondMomentShifts) : ℂ :=
  zetaChi (secondSourceZetaPoints t 0+α 0)*
    zetaChi (secondSourceZetaPoints t 1+α 1)

theorem secondDualMultiplier_eq_centering (T t : ℝ) (σ : SecondMomentShifts) :
    secondDualMultiplier t (rawSecondMomentShifts T σ) =
      Complex.exp (-(σ 0+σ 1))*centeringFactor T t (σ 0)*
        conj (centeringFactor T t (conj (σ 1))) := by
  have hlow : zetaChi (1-criticalLinePoint t+σ 1/(Real.log T:ℂ)) =
      conj (zetaChi (criticalLinePoint t+conj (σ 1)/(Real.log T:ℂ))) := by
    rw [←zetaChi_conj, criticalLinePoint_one_sub]
    congr 1
    simp
  have hc : criticalChi t*conj (criticalChi t) = 1 := by
    simp [Complex.mul_conj', criticalChi_norm]
  unfold secondDualMultiplier rawSecondMomentShifts
  simp only [secondSourceZetaPoints, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hlow, zetaChi_shift_eq_centeringFactor, zetaChi_shift_eq_centeringFactor]
  simp only [map_mul, ←Complex.exp_conj, map_neg, Complex.conj_conj]
  calc
    _ = (Complex.exp (-(σ 0))*Complex.exp (-(σ 1)))*
        (criticalChi t*conj (criticalChi t))*
        (centeringFactor T t (σ 0)*conj (centeringFactor T t (conj (σ 1)))) := by ring
    _ = _ := by
      rw [hc, mul_one, ←Complex.exp_add,
        show -(σ 0)+-(σ 1) = -(σ 0+σ 1) by ring]
      ring

theorem secondDualMultiplier_uniform_normalized_error {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ x ∈ Icc (1:ℝ) 2, ∀ σ : SecondMomentShifts,
        (∀ j, ‖σ j‖ ≤ R) →
        ‖secondDualMultiplier (T*x) (rawSecondMomentShifts T σ)-
          Complex.exp (-(σ 0+σ 1))‖ ≤ C/Real.log T := by
  have hC : 0 ≤ centeringUniformConstant R := by
    unfold centeringUniformConstant centeringPhaseComplexBound
    have hp : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  refine ⟨3*centeringUniformConstant R*Real.exp (2*R), by positivity, ?_⟩
  filter_upwards [centeringFactor_uniform_disk_bound R,
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (max 1 (centeringUniformConstant R)))] with T hb hL
  intro x hx σ hσ
  have hLp : 0 < Real.log T := by linarith [(le_max_left (1:ℝ) _).trans hL]
  let E : ℝ := centeringUniformConstant R/Real.log T
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hE1 : E ≤ 1 := by
    dsimp [E]
    rw [div_le_iff₀ hLp]
    simpa only [one_mul] using
      (le_max_right (1:ℝ) (centeringUniformConstant R)).trans hL
  let r : Fin 2 → ℂ := ![centeringFactor T (T*x) (σ 0),
    conj (centeringFactor T (T*x) (conj (σ 1)))]
  have hr : ∀ j, ‖r j-1‖ ≤ E := by
    intro j
    fin_cases j
    · exact hb x hx (σ 0) (hσ 0)
    · change ‖conj (centeringFactor T (T*x) (conj (σ 1)))-1‖ ≤ E
      rw [show conj (centeringFactor T (T*x) (conj (σ 1)))-1 =
        conj (centeringFactor T (T*x) (conj (σ 1))-1) by simp, Complex.norm_conj]
      exact hb x hx (conj (σ 1)) (by simpa using hσ 1)
  have hp := twofold_product_error_le r hE hE1 hr
  have hexp : ‖Complex.exp (-(σ 0+σ 1))‖ ≤ Real.exp (2*R) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h0 := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hσ 0))).1
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans (hσ 1))).1
    simp only [Complex.neg_re, Complex.add_re]
    linarith
  rw [secondDualMultiplier_eq_centering]
  have he : Complex.exp (-(σ 0+σ 1))*centeringFactor T (T*x) (σ 0)*
      conj (centeringFactor T (T*x) (conj (σ 1)))-Complex.exp (-(σ 0+σ 1)) =
      Complex.exp (-(σ 0+σ 1))*((∏ j : Fin 2, r j)-1) := by
    simp [r, Fin.prod_univ_succ]
    ring
  rw [he, norm_mul]
  exact (mul_le_mul hexp hp (norm_nonneg _) (Real.exp_pos _).le).trans_eq
    (by dsimp [E]; ring)

theorem secondDualMultiplier_uniform_normalized_tendsto {R : ℝ} (hR : 0 ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc (1:ℝ) 2, ∀ σ : SecondMomentShifts,
      (∀ j, ‖σ j‖ ≤ R) →
      ‖secondDualMultiplier (T*x) (rawSecondMomentShifts T σ)-
        Complex.exp (-(σ 0+σ 1))‖ < ε := by
  obtain ⟨C, _hC, hb⟩ := secondDualMultiplier_uniform_normalized_error hR
  have ht : Tendsto (fun T : ℝ => C/Real.log T) atTop (𝓝 0) := by
    have hi : Tendsto (fun T : ℝ => (Real.log T)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    simpa only [div_eq_mul_inv, mul_zero] using
      hi.const_mul C
  filter_upwards [hb, ht.eventually_lt_const hε] with T hb hT
  intro x hx σ hσ
  exact (hb x hx σ hσ).trans_lt hT

end
end Sechstmoment.Source
