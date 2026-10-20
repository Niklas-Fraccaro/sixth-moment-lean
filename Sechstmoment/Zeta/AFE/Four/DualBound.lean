import Sechstmoment.Zeta.AFE.Four.Definitions
import Sechstmoment.Zeta.Moments.CenteringRemainder


namespace Sechstmoment
open Complex Source Set Filter
open scoped BigOperators Topology ComplexConjugate
noncomputable section

theorem zetaChi_shift_eq_centeringFactor (T t : ℝ) (z : ℂ) :
    zetaChi (criticalLinePoint t+z/(Real.log T : ℂ)) =
      Complex.exp (-z)*criticalChi t*centeringFactor T t z := by
  have hn := criticalChi_ne_zero t
  have he : criticalChi t*centeringFactor T t z =
      Complex.exp z*zetaChi (criticalLinePoint t+z/(Real.log T : ℂ)) := by
    unfold centeringFactor centeringShift
    field_simp
  rw [mul_assoc,he,← mul_assoc,← Complex.exp_add]
  simp

theorem sourceZetaPoints_shifted_chi_uniform_bound {R : ℝ} (_hR : 0 ≤ R) :
    ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc (1 : ℝ) 2, ∀ z : ℂ, ‖z‖ ≤ R →
      ∀ j : Fin 4,
      ‖zetaChi (sourceZetaPoints (T*x) j+z/(Real.log T : ℂ))‖ ≤ 2*Real.exp R := by
  filter_upwards [centeringFactor_uniform_disk_bound R,
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (max 1 (centeringUniformConstant R)))] with T hb hL
  have hLpos : 0 < Real.log T := by
    linarith [(le_max_left (1 : ℝ) _).trans hL]
  have hCL : centeringUniformConstant R/Real.log T ≤ 1 := by
    apply (div_le_iff₀ hLpos).mpr
    simpa using (le_max_right (1 : ℝ) _).trans hL
  have hu : ∀ x ∈ Icc (1 : ℝ) 2, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖zetaChi (criticalLinePoint (T*x)+z/(Real.log T : ℂ))‖ ≤ 2*Real.exp R := by
    intro x hx z hz
    have hcen : ‖centeringFactor T (T*x) z‖ ≤ 2 := by
      have hn := norm_add_le (centeringFactor T (T*x) z-1) (1 : ℂ)
      simp only [sub_add_cancel,norm_one] at hn
      linarith [hb x hx z hz]
    have he : ‖Complex.exp (-z)‖ ≤ Real.exp R := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      have hr := (abs_le.mp ((Complex.abs_re_le_norm z).trans hz)).1
      simp only [neg_re]
      linarith
    rw [zetaChi_shift_eq_centeringFactor,norm_mul,norm_mul,criticalChi_norm,mul_one]
    calc
      _ ≤ Real.exp R*2 := mul_le_mul he hcen (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
  have hl : ∀ x ∈ Icc (1 : ℝ) 2, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖zetaChi (1-criticalLinePoint (T*x)+z/(Real.log T : ℂ))‖ ≤ 2*Real.exp R := by
    intro x hx z hz
    have he : zetaChi (1-criticalLinePoint (T*x)+z/(Real.log T : ℂ)) =
        conj (zetaChi (criticalLinePoint (T*x)+conj z/(Real.log T : ℂ))) := by
      rw [← zetaChi_conj,criticalLinePoint_one_sub]
      congr 1
      simp
    rw [he,Complex.norm_conj]
    exact hu x hx (conj z) (by simpa using hz)
  intro x hx z hz j
  fin_cases j <;> simp [sourceZetaPoints] <;>
    first | exact hu x hx z hz | exact hl x hx z hz

theorem bblrDualMultiplier_uniform_normalized_bound
    (K : Set MomentShifts) (hK : IsCompact K) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ t ∈ Icc T (2*T),
      ‖bblrDualMultiplier t (rawMomentShifts T σ)‖ ≤ D := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R : ℝ := max B 0
  have hR : 0 ≤ R := le_max_right _ _
  refine ⟨(2*Real.exp R)^4,by positivity,?_⟩
  filter_upwards [sourceZetaPoints_shifted_chi_uniform_bound hR,
    eventually_gt_atTop (0 : ℝ)] with T hb hT
  intro σ hσ t ht
  have hx : t/T ∈ Icc (1 : ℝ) 2 := by
    constructor
    · exact (le_div_iff₀ hT).mpr (by simpa using ht.1)
    · exact (div_le_iff₀ hT).mpr (by linarith [ht.2])
  have hj : ∀ j, ‖σ j‖ ≤ R := fun j =>
    ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  unfold bblrDualMultiplier
  rw [norm_prod]
  calc
    _ ≤ ∏ _j : Fin 4, (2*Real.exp R) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j _
      have h := hb (t/T) hx (σ j) (hj j) j
      simpa only [rawMomentShifts,mul_div_cancel₀ t hT.ne'] using h
    _ = _ := by simp

end
end Sechstmoment
