import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Tactic
import SixthMoment.Zeta.Moments.SixTerms


namespace SixthMoment

open Complex
open scoped BigOperators

noncomputable section

abbrev PurePolarIndex := Fin 6 × Fin 2 × Fin 2

def purePolarLeft (i : Fin 2) : Fin 4 := ⟨i.val, by omega⟩
def purePolarRight (j : Fin 2) : Fin 4 := ⟨j.val+2, by omega⟩

def purePolarRoot (T : ℝ) (σ : MomentShifts) (k : PurePolarIndex) : ℂ :=
  -(Source.bblrSixShifts (rawMomentShifts T σ) k.1 (purePolarLeft k.2.1) +
    Source.bblrSixShifts (rawMomentShifts T σ) k.1 (purePolarRight k.2.2))/2

def polarPoleKillingFactor (ρ z : ℂ) : ℂ :=
  if ρ = 0 then 1 else 1-z^2/ρ^2

def polarPoleKiller (T : ℝ) (σ : MomentShifts) (z : ℂ) : ℂ :=
  Complex.exp (z^2) * ∏ k : PurePolarIndex, polarPoleKillingFactor (purePolarRoot T σ k) z

theorem purePolarRoot_pole_equation (T : ℝ) (σ : MomentShifts) (k : PurePolarIndex) :
    2*purePolarRoot T σ k +
      Source.bblrSixShifts (rawMomentShifts T σ) k.1 (purePolarLeft k.2.1) +
      Source.bblrSixShifts (rawMomentShifts T σ) k.1 (purePolarRight k.2.2) = 0 := by
  unfold purePolarRoot
  ring

@[simp] theorem polarPoleKillingFactor_zero (ρ : ℂ) :
    polarPoleKillingFactor ρ 0 = 1 := by
  simp [polarPoleKillingFactor]

@[simp] theorem polarPoleKiller_zero (T : ℝ) (σ : MomentShifts) :
    polarPoleKiller T σ 0 = 1 := by
  simp [polarPoleKiller]

theorem polarPoleKiller_even (T : ℝ) (σ : MomentShifts) (z : ℂ) :
    polarPoleKiller T σ (-z) = polarPoleKiller T σ z := by
  simp [polarPoleKiller, polarPoleKillingFactor]

theorem polarPoleKillingFactor_eq_zero_iff {ρ z : ℂ} (hρ : ρ ≠ 0) :
    polarPoleKillingFactor ρ z = 0 ↔ z = ρ ∨ z = -ρ := by
  rw [polarPoleKillingFactor, ite_eq_right hρ]
  have hp : ρ^2 ≠ 0 := pow_ne_zero _ hρ
  rw [sub_eq_zero, eq_comm, div_eq_one_iff_eq hp, sq_eq_sq_iff_eq_or_eq_neg]

theorem polarPoleKiller_eq_zero_iff (T : ℝ) (σ : MomentShifts) (z : ℂ) :
    polarPoleKiller T σ z = 0 ↔ ∃ k : PurePolarIndex,
      purePolarRoot T σ k ≠ 0 ∧ (z = purePolarRoot T σ k ∨ z = -purePolarRoot T σ k) := by
  rw [polarPoleKiller, mul_eq_zero, or_iff_right (Complex.exp_ne_zero _),
    Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, _, hk⟩
    have hr : purePolarRoot T σ k ≠ 0 := by
      intro hr
      simp [polarPoleKillingFactor, hr] at hk
    exact ⟨k, hr, (polarPoleKillingFactor_eq_zero_iff hr).mp hk⟩
  · rintro ⟨k, hr, hk⟩
    exact ⟨k, Finset.mem_univ k, (polarPoleKillingFactor_eq_zero_iff hr).mpr hk⟩

theorem polarPoleKiller_at_root (T : ℝ) (σ : MomentShifts) (k : PurePolarIndex)
    (hk : purePolarRoot T σ k ≠ 0) :
    polarPoleKiller T σ (purePolarRoot T σ k) = 0 :=
  (polarPoleKiller_eq_zero_iff T σ _).mpr ⟨k, hk, Or.inl rfl⟩

theorem polarPoleKiller_differentiable (T : ℝ) (σ : MomentShifts) :
    Differentiable ℂ (polarPoleKiller T σ) := by
  unfold polarPoleKiller
  refine (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (z^2))).mul ?_
  apply Differentiable.fun_finsetProd
  intro k _
  change Differentiable ℂ (fun z : ℂ =>
    if purePolarRoot T σ k = 0 then 1 else 1-z^2/(purePolarRoot T σ k)^2)
  by_cases hk : purePolarRoot T σ k = 0
  · simp only [ite_eq_left hk]
    fun_prop
  · simp only [ite_eq_right hk]
    fun_prop

theorem polarPoleKillingFactor_factorization {ρ : ℂ} (hρ : ρ ≠ 0) (z : ℂ) :
    polarPoleKillingFactor ρ z =
      (2*(z-ρ)) * (-(z+ρ)/(2*ρ^2)) := by
  rw [polarPoleKillingFactor, ite_eq_right hρ]
  field_simp
  ring

def purePolarTermKiller (T : ℝ) (σ : MomentShifts) (m : Fin 6) (z : ℂ) : ℂ :=
  ∏ ij : Fin 2 × Fin 2, polarPoleKillingFactor (purePolarRoot T σ (m,ij)) z

def purePolarTermDivisor (T : ℝ) (σ : MomentShifts) (m : Fin 6) (z : ℂ) : ℂ :=
  ∏ ij : Fin 2 × Fin 2, 2*(z-purePolarRoot T σ (m,ij))

def purePolarTermRemovedKiller (T : ℝ) (σ : MomentShifts) (m : Fin 6) (z : ℂ) : ℂ :=
  ∏ ij : Fin 2 × Fin 2,
    -(z+purePolarRoot T σ (m,ij))/(2*(purePolarRoot T σ (m,ij))^2)

theorem purePolarTermKiller_factorization (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0) (z : ℂ) :
    purePolarTermKiller T σ m z =
      purePolarTermDivisor T σ m z * purePolarTermRemovedKiller T σ m z := by
  unfold purePolarTermKiller purePolarTermDivisor purePolarTermRemovedKiller
  simp_rw [polarPoleKillingFactor_factorization (hρ _)]
  exact Finset.prod_mul_distrib

theorem purePolarTermRemovedKiller_differentiable (T : ℝ) (σ : MomentShifts) (m : Fin 6) :
    Differentiable ℂ (purePolarTermRemovedKiller T σ m) := by
  unfold purePolarTermRemovedKiller
  fun_prop

theorem polarPoleKillingFactor_norm_le (ρ z : ℂ) :
    ‖polarPoleKillingFactor ρ z‖ ≤
      if ρ = 0 then 1 else 1+‖z‖^2/‖ρ‖^2 := by
  by_cases hρ : ρ = 0
  · simp [polarPoleKillingFactor, hρ]
  · simp only [polarPoleKillingFactor, ite_eq_right hρ]
    calc
      ‖1-z^2/ρ^2‖ ≤ ‖(1:ℂ)‖+‖z^2/ρ^2‖ := norm_sub_le _ _
      _ = 1+‖z‖^2/‖ρ‖^2 := by rw [norm_one, Complex.norm_div, Complex.norm_pow, Complex.norm_pow]

theorem polarPoleKiller_norm_vertical_le (T : ℝ) (σ : MomentShifts) (c t : ℝ) :
    ‖polarPoleKiller T σ ((c:ℂ)+t*I)‖ ≤ Real.exp (c^2-t^2) *
      ∏ k : PurePolarIndex, if purePolarRoot T σ k = 0 then 1
        else 1+(c^2+t^2)/‖purePolarRoot T σ k‖^2 := by
  have hre : (((c:ℂ)+t*I)^2).re = c^2-t^2 := by
    simp [pow_two]
  have hnorm : ‖(c:ℂ)+t*I‖^2 = c^2+t^2 := by
    simp [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [polarPoleKiller, norm_mul, Complex.norm_exp, norm_prod, hre]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.prod_le_prod₀
  · intro k _
    exact norm_nonneg _
  · intro k _
    simpa only [hnorm] using polarPoleKillingFactor_norm_le
      (purePolarRoot T σ k) ((c:ℂ)+t*I)

end

end SixthMoment
