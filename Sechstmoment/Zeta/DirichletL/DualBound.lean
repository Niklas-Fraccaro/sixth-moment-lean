import Sechstmoment.Zeta.DirichletL.RootNumber
import Sechstmoment.Zeta.DirichletL.Weights.Bounds


namespace Sechstmoment.Source
open Complex Real MeasureTheory Filter Set ComplexConjugate
open scoped Topology BigOperators Classical
noncomputable section

theorem gammaR_dual_ratio_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (3/4) →
      ∀ a : ℕ, a ≤ 1 →
      ‖Complex.Gammaℝ (1-s+(a : ℂ))/Complex.Gammaℝ (s+(a : ℂ))‖ ≤
        C*(1+|s.im|)^2 := by
  obtain ⟨C,hC,hbound⟩ := gamma_compact_strip_quotient_bound
    (1/8) (7/8) (by norm_num) (by norm_num)
  refine ⟨Real.pi*C, by positivity, ?_⟩
  intro s hs a ha
  let z : ℂ := (1-conj s+(a : ℂ))/2
  let w : ℂ := (s+(a : ℂ))/2
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have ha1 : (a : ℝ) ≤ 1 := by exact_mod_cast ha
  have hz : z.re ∈ Icc (1/8 : ℝ) (7/8) := by
    dsimp [z]
    simp only [Complex.div_ofNat_re, add_re, sub_re, one_re, conj_re, natCast_re]
    constructor <;> linarith [hs.1,hs.2]
  have hw : w.re ∈ Icc (1/8 : ℝ) (7/8) := by
    dsimp [w]
    simp only [Complex.div_ofNat_re, add_re, natCast_re]
    constructor <;> linarith [hs.1,hs.2]
  have h := hbound z w hz hw
  have him : z.im-w.im = 0 := by simp [z,w]
  rw [him, abs_zero, mul_zero, zero_div, Real.exp_zero, mul_one] at h
  have hzi : |z.im| ≤ |s.im| := by norm_num [z,abs_div]
  have hwi : |w.im| ≤ |s.im| := by norm_num [w,abs_div]
  have hΓ : ‖Complex.Gamma ((1-s+(a : ℂ))/2)/Complex.Gamma ((s+(a : ℂ))/2)‖ ≤
      C*(1+|s.im|)^2 := by
    have he : (1-s+(a : ℂ))/2 = conj z := by
      apply Complex.ext <;>
        simp only [z, Complex.conj_re, Complex.conj_im, Complex.div_ofNat_re,
          Complex.div_ofNat_im, Complex.add_re, Complex.add_im, Complex.sub_re,
          Complex.sub_im, Complex.one_re, Complex.one_im, Complex.natCast_re,
          Complex.natCast_im]
      ring
    rw [he, Complex.Gamma_conj, norm_div, norm_conj]
    change ‖Complex.Gamma z‖/‖Complex.Gamma w‖ ≤ _
    rw [← norm_div]
    exact h.trans (by nlinarith [mul_le_mul hzi hwi (abs_nonneg _) (abs_nonneg _)])
  have hpi : Real.pi^(s.re-1/2) ≤ Real.pi := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith [Real.two_le_pi] : 1 ≤ Real.pi)
      (show s.re-1/2 ≤ 1 by linarith [hs.2])
    simpa only [Real.rpow_one] using h
  have heq : ‖Complex.Gammaℝ (1-s+(a : ℂ))/Complex.Gammaℝ (s+(a : ℂ))‖ =
      Real.pi^(s.re-1/2)*
        ‖Complex.Gamma ((1-s+(a : ℂ))/2)/Complex.Gamma ((s+(a : ℂ))/2)‖ := by
    rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, norm_div, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, mul_div_mul_comm,
      ← Real.rpow_sub Real.pi_pos, norm_div]
    congr 2
    simp only [Complex.div_ofNat_re, neg_re, add_re, sub_re, one_re, natCast_re]
    ring
  rw [heq]
  calc
    _ ≤ Real.pi*(C*(1+|s.im|)^2) := mul_le_mul hpi hΓ (norm_nonneg _) Real.pi_pos.le
    _ = _ := by ring

theorem dirichletGammaFactor_eq_gammaR_parity {N : ℕ}
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    χ.gammaFactor s = Complex.Gammaℝ (s+(dirichletParity χ : ℂ)) := by
  unfold DirichletCharacter.gammaFactor dirichletParity
  split_ifs <;> simp

theorem conductorGamma_dual_ratio_norm {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (s : ℂ) :
    ‖conductorGammaFactor χ⁻¹ (1-s)/conductorGammaFactor χ s‖ =
      (N : ℝ)^(1/2-s.re)*‖χ⁻¹.gammaFactor (1-s)/χ.gammaFactor s‖ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [conductorGammaFactor, conductorGammaFactor, norm_div, norm_mul, norm_mul,
    show (N : ℂ) = ((N : ℝ) : ℂ) by norm_cast,
    Complex.norm_cpow_eq_rpow_re_of_pos hN, Complex.norm_cpow_eq_rpow_re_of_pos hN,
    mul_div_mul_comm, ← Real.rpow_sub hN, norm_div]
  congr 2
  simp only [Complex.div_ofNat_re, sub_re, one_re]
  ring

theorem dirichletSquareDualFactor_norm_sq_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ _ : NeZero N,
      ∀ χ : DirichletCharacter ℂ N, χ.IsPrimitive →
      ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (3/4) →
      ‖dirichletSquareDualFactor χ s‖^2 ≤
        C*(N : ℝ)^(1-2*s.re)*(1+|s.im|)^4 := by
  obtain ⟨C,hC,hbound⟩ := gammaR_dual_ratio_bound
  refine ⟨C^2, by positivity, ?_⟩
  intro N hN χ hχ s hs
  have : NeZero N := hN
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hΓ := hbound s hs (dirichletParity χ) (dirichletParity_le_one χ)
  have hnorm : ‖dirichletSquareDualFactor χ s‖ =
      (N : ℝ)^(1/2-s.re)*‖χ⁻¹.gammaFactor (1-s)/χ.gammaFactor s‖ := by
    rw [dirichletSquareDualFactor, mul_div_assoc, norm_mul, primitive_rootNumber_norm χ hχ,
      one_mul, conductorGamma_dual_ratio_norm]
  rw [dirichletGammaFactor_eq_gammaR_parity, dirichletGammaFactor_eq_gammaR_parity,
    dirichletParity_inv] at hnorm
  have hp : ((N : ℝ)^(1/2-s.re))^2 = (N : ℝ)^(1-2*s.re) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    ring
  rw [hnorm]
  calc
    _ ≤ ((N : ℝ)^(1/2-s.re)*(C*(1+|s.im|)^2))^2 := by gcongr
    _ = _ := by rw [mul_pow, hp]; ring

end
end Sechstmoment.Source
