import Mathlib.Tactic
import Sechstmoment.Arithmetic.Euler.Shifted.Uniform

/-!
# The actual arithmetic-factor limit on rescaled polar contours

Continuity of the convergent six-variable shifted product gives uniform
convergence to `a₃` on every bounded set of normalized shifts.
-/

namespace Sechstmoment

open Real Complex Filter Set
open scoped BigOperators Topology

noncomputable section

def scaledPolarShifts (L : ℝ) (ab : PolarShiftSpace) : PolarShiftSpace := (L:ℂ)⁻¹ • ab

theorem scaledPolarShifts_fst (L : ℝ) (ab : PolarShiftSpace) (i : Fin 3) :
    (scaledPolarShifts L ab).1 i = ab.1 i/(L:ℂ) := by
  simp only [scaledPolarShifts, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem scaledPolarShifts_snd (L : ℝ) (ab : PolarShiftSpace) (i : Fin 3) :
    (scaledPolarShifts L ab).2 i = ab.2 i/(L:ℂ) := by
  simp only [scaledPolarShifts, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem shiftedPolarEulerRest_scaled_uniform {K : Set PolarShiftSpace}
    (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn
      (fun L : ℝ => fun ab : PolarShiftSpace =>
        shiftedPolarEulerRest (scaledPolarShifts L ab).1 (scaledPolarShifts L ab).2)
      (fun _ => (arithmeticFactor:ℂ)) atTop K := by
  obtain ⟨C, hC, hbound⟩ := hK.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp
    shiftedPolarEulerRest_continuousAt_zero ε hε
  filter_upwards [eventually_gt_atTop (max 1 (C/δ))] with L hL ab hab
  have hLp : 0 < L := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_left _ _) hL)
  have hLC : C/δ < L := lt_of_le_of_lt (le_max_right _ _) hL
  have hsmall : dist (scaledPolarShifts L ab) ((fun _ => 0), (fun _ => 0)) < δ := by
    change dist (scaledPolarShifts L ab) (0:PolarShiftSpace) < δ
    rw [dist_zero_right, scaledPolarShifts, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hLp.le]
    calc
      L⁻¹*‖ab‖ ≤ L⁻¹*C := by gcongr; exact hbound ab hab
      _ < δ := by
        rw [inv_mul_eq_div]
        exact (div_lt_iff₀ hLp).mpr (by
          have h := (div_lt_iff₀ hδ).mp hLC
          nlinarith)
  simpa only [shiftedPolarEulerRest_zero, dist_comm] using hcont hsmall

theorem shiftedPolarEulerRest_scaled_tendsto (ab : PolarShiftSpace) :
    Tendsto (fun L : ℝ => shiftedPolarEulerRest
      (scaledPolarShifts L ab).1 (scaledPolarShifts L ab).2) atTop
      (𝓝 (arithmeticFactor:ℂ)) :=
  (shiftedPolarEulerRest_scaled_uniform (isCompact_singleton.isBounded :
    Bornology.IsBounded ({ab}:Set PolarShiftSpace))).tendsto_at (mem_singleton ab)

end

end Sechstmoment
