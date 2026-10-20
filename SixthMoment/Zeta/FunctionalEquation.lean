import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import SixthMoment.Analysis.Complex.PhaseProjection


namespace SixthMoment

open Complex MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

def criticalLinePoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I

@[simp] theorem criticalLinePoint_re (t : ℝ) : (criticalLinePoint t).re = 1 / 2 := by
  simp [criticalLinePoint]

@[simp] theorem criticalLinePoint_im (t : ℝ) : (criticalLinePoint t).im = t := by
  simp [criticalLinePoint]

theorem criticalLinePoint_ne_zero (t : ℝ) : criticalLinePoint t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

theorem criticalLinePoint_ne_one (t : ℝ) : criticalLinePoint t ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

theorem criticalLinePoint_one_sub (t : ℝ) :
    1 - criticalLinePoint t = star (criticalLinePoint t) := by
  apply Complex.ext
  · simp [criticalLinePoint]
    ring
  · simp [criticalLinePoint]

private theorem real_cpow_conj {a : ℝ} (ha : 0 < a) (s : ℂ) :
    (a : ℂ) ^ conj s = conj ((a : ℂ) ^ s) := by
  have harg : (a : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg ha.le]
    exact Real.pi_pos.ne
  simpa only [conj_ofReal] using cpow_conj (a : ℂ) s harg

private theorem mellin_conj_of_real (f : ℝ → ℂ)
    (hf : ∀ x, conj (f x) = f x) (s : ℂ) :
    mellin f (conj s) = conj (mellin f s) := by
  rw [mellin, mellin, ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul, map_mul, hf]
  rw [← real_cpow_conj hx, map_sub, map_one]

theorem completedRiemannZeta₀_conj (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) := by
  have hf : ∀ x : ℝ, conj ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
    intro x
    simp [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
      Set.indicator_apply, smul_eq_mul]
    split_ifs <;> simp
  change (HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ (conj s / 2) / 2 =
    conj ((HurwitzZeta.hurwitzEvenFEPair 0).Λ₀ (s / 2) / 2)
  simp only [map_div₀, map_ofNat]
  congr 1
  have hdiv : conj (s / 2) = conj s / 2 := by rw [map_div₀, map_ofNat]
  rw [← hdiv]
  exact mellin_conj_of_real _ hf _

theorem completedRiemannZeta_conj (s : ℂ) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) := by
  simp only [completedRiemannZeta_eq, completedRiemannZeta₀_conj,
    map_sub, map_div₀, map_one]

theorem gammaReal_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  simp only [Gammaℝ_def, map_mul, map_div₀, map_ofNat, ← Gamma_conj]
  rw [← real_cpow_conj Real.pi_pos, map_div₀, map_neg, map_ofNat]

theorem riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by
  by_cases hs : s = 0
  · subst s
    simp [riemannZeta_zero, map_ofNat]
  · have hc : conj s ≠ 0 := by simpa using hs
    rw [riemannZeta_def_of_ne_zero hs, riemannZeta_def_of_ne_zero hc,
      completedRiemannZeta_conj, gammaReal_conj, map_div₀]

def criticalChi (t : ℝ) : ℂ :=
  Gammaℝ (1 - criticalLinePoint t) / Gammaℝ (criticalLinePoint t)

theorem criticalChi_gamma_formula (t : ℝ) :
    criticalChi t = 2 * (2 * Real.pi : ℂ) ^ (criticalLinePoint t - 1) *
      Gamma (1 - criticalLinePoint t) * sin (Real.pi * criticalLinePoint t / 2) := by
  have hs : ∀ n : ℕ, 1 - criticalLinePoint t ≠ -(2 * n + 1) := by
    intro n h
    have hr := congrArg Complex.re h
    norm_num at hr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := Gammaℝ_div_Gammaℝ_one_sub hs
  rw [sub_sub_cancel] at h
  change Gammaℝ (1 - criticalLinePoint t) / Gammaℝ (criticalLinePoint t) = _
  rw [h, Gammaℂ_def]
  have he : -(1 - criticalLinePoint t) = criticalLinePoint t - 1 := by ring
  have hc : (Real.pi : ℂ) * (1 - criticalLinePoint t) / 2 =
      (Real.pi : ℂ) / 2 - Real.pi * criticalLinePoint t / 2 := by ring
  rw [he, hc, Complex.cos_pi_div_two_sub]

theorem gammaReal_criticalLinePoint_ne_zero (t : ℝ) :
    Gammaℝ (criticalLinePoint t) ≠ 0 := by
  apply Gammaℝ_ne_zero_of_re_pos
  rw [criticalLinePoint_re]
  norm_num

theorem criticalChi_eq_conj_div (t : ℝ) :
    criticalChi t = star (Gammaℝ (criticalLinePoint t)) / Gammaℝ (criticalLinePoint t) := by
  rw [criticalChi, criticalLinePoint_one_sub]
  exact congrArg (fun z : ℂ => z / Gammaℝ (criticalLinePoint t))
    (gammaReal_conj (criticalLinePoint t))

theorem criticalChi_mul_star (t : ℝ) : criticalChi t * star (criticalChi t) = 1 := by
  rw [criticalChi_eq_conj_div]
  simp only [star_div₀, star_star]
  have h := gammaReal_criticalLinePoint_ne_zero t
  have hc : star (Gammaℝ (criticalLinePoint t)) ≠ 0 := by simpa using h
  field_simp

theorem criticalChi_norm (t : ℝ) : ‖criticalChi t‖ = 1 := by
  have h := congrArg norm (criticalChi_mul_star t)
  simp only [norm_mul, norm_star, norm_one] at h
  nlinarith [norm_nonneg (criticalChi t)]

theorem riemannZeta_critical_functional_equation (t : ℝ) :
    riemannZeta (criticalLinePoint t) =
      criticalChi t * riemannZeta (1 - criticalLinePoint t) := by
  have hs := criticalLinePoint_ne_zero t
  have hs' : 1 - criticalLinePoint t ≠ 0 := by
    rw [criticalLinePoint_one_sub]
    simpa using hs
  have hg := gammaReal_criticalLinePoint_ne_zero t
  have hg' : Gammaℝ (1 - criticalLinePoint t) ≠ 0 := by
    rw [criticalLinePoint_one_sub]
    change Gammaℝ (conj (criticalLinePoint t)) ≠ 0
    rw [gammaReal_conj]
    simpa using hg
  rw [riemannZeta_def_of_ne_zero hs, criticalChi, riemannZeta_def_of_ne_zero hs',
    completedRiemannZeta_one_sub]
  field_simp

theorem riemannZeta_critical_real_structure (t : ℝ) :
    riemannZeta (criticalLinePoint t) =
      criticalChi t * star (riemannZeta (criticalLinePoint t)) := by
  calc
    riemannZeta (criticalLinePoint t) =
        criticalChi t * riemannZeta (1 - criticalLinePoint t) :=
      riemannZeta_critical_functional_equation t
    _ = criticalChi t * star (riemannZeta (criticalLinePoint t)) := by
      congr 1
      rw [criticalLinePoint_one_sub]
      exact riemannZeta_conj (criticalLinePoint t)

theorem zeta_phaseProjection_mixed_re (t : ℝ) (F : ℂ) :
    riemannZeta (criticalLinePoint t) ^ 3 * star (phaseProjection (criticalChi t) F) =
      ((riemannZeta (criticalLinePoint t) ^ 3 * star F).re : ℂ) :=
  phaseProjection_mixed_re (criticalChi_mul_star t) (riemannZeta_critical_real_structure t)

theorem zeta_phaseProjection_gram (t : ℝ) (F G : ℂ) :
    phaseProjection (criticalChi t) F * star (phaseProjection (criticalChi t) G) =
      (1 / 2 : ℂ) * ((F * star G + (star (criticalChi t)) ^ 3 * F * G).re : ℂ) :=
  phaseProjection_gram (criticalChi_mul_star t)

theorem zeta_phaseProjection_real_structure (t : ℝ) (F : ℂ) :
    phaseProjection (criticalChi t) F =
      criticalChi t ^ 3 * star (phaseProjection (criticalChi t) F) :=
  phaseProjection_phase (criticalChi_mul_star t)

theorem zeta_phaseProjection_idempotent (t : ℝ) (F : ℂ) :
    phaseProjection (criticalChi t) (phaseProjection (criticalChi t) F) =
      phaseProjection (criticalChi t) F :=
  phaseProjection_idempotent (criticalChi_mul_star t)

end

end SixthMoment
