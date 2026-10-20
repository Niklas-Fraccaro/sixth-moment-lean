import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic
import SixthMoment.Zeta.CompletedBounds


namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped Topology BigOperators
noncomputable section

theorem completedHurwitzEven_entire_strip_bound (a : UnitAddCircle) (u v : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      ‖HurwitzZeta.completedHurwitzZetaEven₀ a s‖ ≤ C := by
  let P := HurwitzZeta.hurwitzEvenFEPair a
  have hm (s : ℂ) : MellinConvergent P.f_modif s :=
    (P.isStrongFEPair_toStrongFEPair.hasMellin s).1
  refine ⟨mellinStripMajorant P.f_modif (u/2) (v/2) / 2,
    div_nonneg (mellinStripMajorant_nonneg _ _ _) (by norm_num), ?_⟩
  intro s hsu hsv
  have h := mellin_norm_le_strip_majorant P.f_modif (u/2) (v/2)
    (hm _) (hm _) (hm (s/2))
    (by simp only [Complex.div_ofNat_re]; linarith)
    (by simp only [Complex.div_ofNat_re]; linarith)
  change ‖mellin P.f_modif (s/2) / 2‖ ≤ _
  rw [norm_div]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem completedHurwitzOdd_strip_bound (a : UnitAddCircle) (u v : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      ‖HurwitzZeta.completedHurwitzZetaOdd a s‖ ≤ C := by
  let P := HurwitzZeta.hurwitzOddFEPair a
  have hp : IsStrongFEPair P := HurwitzZeta.isStrong_hurwitzOddFEPair a
  have hm (s : ℂ) : MellinConvergent P.f s := (hp.hasMellin s).1
  refine ⟨mellinStripMajorant P.f ((u+1)/2) ((v+1)/2) / 2,
    div_nonneg (mellinStripMajorant_nonneg _ _ _) (by norm_num), ?_⟩
  intro s hsu hsv
  have h := mellin_norm_le_strip_majorant P.f ((u+1)/2) ((v+1)/2)
    (hm _) (hm _) (hm ((s+1)/2))
    (by simp only [Complex.div_ofNat_re, add_re, one_re]; linarith)
    (by simp only [Complex.div_ofNat_re, add_re, one_re]; linarith)
  unfold HurwitzZeta.completedHurwitzZetaOdd
  change ‖P.Λ ((s+1)/2) / 2‖ ≤ _
  rw [hp.Λ_eq, norm_div]
  norm_num only [Complex.norm_ofNat]
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem completedPeriodicL_entire_strip_bound {N : ℕ} [NeZero N]
    (Φ : ZMod N → ℂ) (u v : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      ‖ZMod.completedLFunction₀ Φ s‖ ≤ C := by
  classical
  choose A hA hAe using fun j : ZMod N =>
    completedHurwitzEven_entire_strip_bound (ZMod.toAddCircle j) u v
  choose B hB hBo using fun j : ZMod N =>
    completedHurwitzOdd_strip_bound (ZMod.toAddCircle j) u v
  let D := (∑ j : ZMod N, ‖Φ j‖*A j) + (∑ j : ZMod N, ‖Φ j‖*B j)
  have hD : 0 ≤ D := by
    exact add_nonneg
      (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hA j))
      (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (hB j))
  refine ⟨(N : ℝ)^(-u)*D, by positivity, ?_⟩
  intro s hsu hsv
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hp : ‖(N : ℂ)^(-s)‖ ≤ (N : ℝ)^(-u) := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos hN, neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  unfold ZMod.completedLFunction₀
  calc
    _ ≤ ‖(N : ℂ)^(-s)‖ *
        (∑ j : ZMod N, ‖Φ j‖ * ‖HurwitzZeta.completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s‖) +
      ‖(N : ℂ)^(-s)‖ *
        (∑ j : ZMod N, ‖Φ j‖ * ‖HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) s‖) := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;>
        rw [norm_mul] <;>
        exact mul_le_mul_of_nonneg_left
          ((norm_sum_le _ _).trans_eq (by simp only [norm_mul])) (norm_nonneg _)
    _ ≤ (N : ℝ)^(-u) * (∑ j : ZMod N, ‖Φ j‖*A j) +
        (N : ℝ)^(-u) * (∑ j : ZMod N, ‖Φ j‖*B j) := by
      gcongr with j
      · exact hAe j s hsu hsv
      · exact hBo j s hsu hsv
    _ = _ := by dsimp [D]; ring

theorem completedDirichletL_strip_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (u v : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      ‖χ.completedLFunction s‖ ≤ C := by
  have hN : N ≠ 1 := by
    intro h
    subst N
    exact hχ (DirichletCharacter.level_one χ)
  obtain ⟨C, hC, hbound⟩ := completedPeriodicL_entire_strip_bound (fun j => χ j) u v
  refine ⟨C, hC, ?_⟩
  intro s hsu hsv
  have he : χ.completedLFunction s = ZMod.completedLFunction₀ (fun j => χ j) s := by
    rw [DirichletCharacter.completedLFunction, ZMod.completedLFunction_eq]
    simp only [χ.map_zero' hN, χ.sum_eq_zero_of_ne_one hχ, mul_zero, zero_div, sub_zero]
  rw [he]
  exact hbound s hsu hsv

def conductorCompletedL {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (N : ℂ)^(s/2) * χ.completedLFunction s

theorem conductorCompletedL_differentiable {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Differentiable ℂ (conductorCompletedL χ) := by
  unfold conductorCompletedL
  apply Differentiable.mul
  · fun_prop
  · exact DirichletCharacter.differentiable_completedLFunction hχ

theorem conductorCompletedL_strip_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (u v : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, u ≤ s.re → s.re ≤ v →
      ‖conductorCompletedL χ s‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := completedDirichletL_strip_bound χ hχ u v
  refine ⟨(N : ℝ)^(v/2)*C, by positivity, ?_⟩
  intro s hsu hsv
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hp : ‖(N : ℂ)^(s/2)‖ ≤ (N : ℝ)^(v/2) := by
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.div_ofNat_re]
    exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  rw [conductorCompletedL, norm_mul]
  exact mul_le_mul hp (hb s hsu hsv) (norm_nonneg _) (by positivity)

theorem conductorCompletedL_one_sub {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hprim : χ.IsPrimitive) (s : ℂ) :
    conductorCompletedL χ (1-s) = χ.rootNumber * conductorCompletedL χ⁻¹ s := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  unfold conductorCompletedL
  rw [hprim.completedLFunction_one_sub]
  rw [← mul_assoc, ← mul_assoc, ← Complex.cpow_add _ _ hN]
  rw [show (1-s)/2+(s-1/2) = s/2 by ring]
  ring

end
end SixthMoment.Source
