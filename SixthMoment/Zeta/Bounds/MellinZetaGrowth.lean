import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import SixthMoment.Zeta.CompletedBounds
import SixthMoment.Zeta.Gamma.MellinBounds


namespace SixthMoment

open Real Complex MeasureTheory Set
open scoped Topology

noncomputable section

theorem realGamma_norm_bounded_on_positive_interval {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, x ∈ Icc a b → Real.Gamma x ≤ C := by
  have hcts : ContinuousOn Real.Gamma (Icc a b) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.mono (fun x hx => ha.trans_le hx.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hcts
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro x hx
  exact (hC ⟨x, hx, rfl⟩).trans (le_max_right _ _)

theorem riemannZeta_norm_le_exp_strip {a b r : ℝ} (ha : 0 < a)
    (hb : b < 2) (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → r ≤ ‖1-s‖ →
      ‖riemannZeta s‖ ≤ C*Real.exp (Real.pi*|s.im|/2) := by
  obtain ⟨K, hK0, hK⟩ := completedRiemannZeta₀_norm_bounded_on_strip a b
  obtain ⟨J, hJ0, hJ⟩ := realGamma_norm_bounded_on_positive_interval
    (a := 1-b/2) (b := 1-a/2) (by linarith)
  let C := (K+1/a+1/r)*(Real.pi^(b/2))*J/Real.pi
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro s hsa hsb hsep
  have hsre : 0 < s.re := ha.trans_le hsa
  have hs0 : s ≠ 0 := by intro h; simp [h] at hsre
  have hsnorm : a ≤ ‖s‖ := hsa.trans (Complex.re_le_norm s)
  have h1 : ‖1/s‖ ≤ 1/a := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le ha hsnorm
  have h2 : ‖1/(1-s)‖ ≤ 1/r := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hr hsep
  have hN : ‖completedRiemannZeta₀ s-1/s-1/(1-s)‖ ≤ K+1/a+1/r := by
    exact (norm_sub_le _ _).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add (hK s hsa hsb) h1)) h2)
  have hGamma : ‖(Complex.Gamma (s/2))⁻¹‖ ≤
      J*Real.exp (Real.pi*|s.im|/2)/Real.pi := by
    have h := gamma_inv_norm_le_exp (s := s/2)
      (by simp only [Complex.div_ofNat_re]; linarith)
      (by simp only [Complex.div_ofNat_re]; linarith)
    have hJ' := hJ (1-(s/2).re)
      (by simp only [Complex.div_ofNat_re]; constructor <;> linarith)
    have hi : Real.pi*|(s/2).im| = Real.pi*|s.im|/2 := by
      rw [Complex.div_ofNat_im, abs_div]
      norm_num
      ring
    rw [hi] at h
    exact h.trans (by gcongr)
  have hPi : ‖((Real.pi:ℂ)^(-s/2))⁻¹‖ ≤ Real.pi^(b/2) := by
    rw [← Complex.cpow_neg]
    have he : -(-s/2) = s/2 := by ring
    rw [he, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.div_ofNat_re]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.two_le_pi]) (by linarith)
  rw [riemannZeta_eq_completedRiemannZeta₀ hs0, div_eq_mul_inv,
    mul_inv_rev, norm_mul, norm_mul]
  calc
    _ ≤ (K+1/a+1/r)*(J*Real.exp (Real.pi*|s.im|/2)/Real.pi * Real.pi^(b/2)) := by
      gcongr
    _ = C*Real.exp (Real.pi*|s.im|/2) := by dsimp [C]; ring

end

end SixthMoment
