import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SixthMoment

open Complex

noncomputable def phaseProjection (χ F : ℂ) : ℂ := (F + χ^3 * star F)/2

theorem phaseProjection_phase {χ F : ℂ} (hχ : χ * star χ = 1) :
    phaseProjection χ F = χ^3 * star (phaseProjection χ F) := by
  have hc : χ^3 * (star χ)^3 = 1 := by rw [← mul_pow, hχ]; norm_num
  simp only [phaseProjection, star_div₀, star_add, star_mul, star_pow, star_star, star_ofNat]
  linear_combination -F/2 * hc

theorem phaseProjection_real_mixed {χ z F : ℂ}
    (hχ : χ * star χ = 1) (hz : z = χ * star z) :
    z^3 * star (phaseProjection χ F) =
      (z^3 * star F + star (z^3 * star F))/2 := by
  have hc : χ^3 * (star χ)^3 = 1 := by rw [← mul_pow, hχ]; norm_num
  have hz3 : z^3 = χ^3 * (star z)^3 := by
    calc
      z^3 = (χ * star z)^3 := congrArg (fun w : ℂ => w^3) hz
      _ = χ^3 * (star z)^3 := by rw [mul_pow]
  have hzχ : z^3 * (star χ)^3 = (star z)^3 := by
    calc
      z^3 * (star χ)^3 = (χ^3 * (star χ)^3) * (star z)^3 := by rw [hz3]; ring
      _ = (star z)^3 := by rw [hc, one_mul]
  simp only [phaseProjection, star_div₀, star_add, star_mul, star_pow, star_star, star_ofNat]
  linear_combination F/2 * hzχ

theorem phaseProjection_idempotent {χ F : ℂ} (hχ : χ * star χ = 1) :
    phaseProjection χ (phaseProjection χ F) = phaseProjection χ F := by
  change (phaseProjection χ F + χ^3 * star (phaseProjection χ F))/2 = phaseProjection χ F
  rw [← phaseProjection_phase hχ]
  ring

theorem phaseProjection_mixed_re {χ z F : ℂ}
    (hχ : χ * star χ = 1) (hz : z = χ * star z) :
    z^3 * star (phaseProjection χ F) = ((z^3 * star F).re : ℂ) := by
  rw [phaseProjection_real_mixed hχ hz]
  exact (RCLike.re_eq_add_conj (z^3 * star F)).symm

theorem phaseProjection_gram {χ F G : ℂ} (hχ : χ * star χ = 1) :
    phaseProjection χ F * star (phaseProjection χ G) =
      (1/2 : ℂ) * ((F * star G + (star χ)^3 * F * G).re : ℂ) := by
  have hc : χ^3 * (star χ)^3 = 1 := by rw [← mul_pow, hχ]; norm_num
  have hre : ((F * star G + (star χ)^3 * F * G).re : ℂ) =
      ((F * star G + (star χ)^3 * F * G) + star (F * star G + (star χ)^3 * F * G))/2 :=
    RCLike.re_eq_add_conj (F * star G + (star χ)^3 * F * G)
  rw [hre]
  simp only [phaseProjection, star_div₀, star_add, star_mul, star_pow, star_star, star_ofNat]
  linear_combination (star F * G / 4) * hc

theorem phaseProjection_add (χ F G : ℂ) :
    phaseProjection χ (F + G) = phaseProjection χ F + phaseProjection χ G := by
  simp only [phaseProjection, star_add]
  ring

theorem phaseProjection_real_smul (χ F : ℂ) (a : ℝ) :
    phaseProjection χ ((a : ℂ) * F) = (a : ℂ) * phaseProjection χ F := by
  have ha : star (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
  simp only [phaseProjection, star_mul, ha]
  ring

end SixthMoment
