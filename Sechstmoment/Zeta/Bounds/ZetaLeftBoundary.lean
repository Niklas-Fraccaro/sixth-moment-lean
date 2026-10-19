import Sechstmoment.Zeta.Bounds.MellinZetaDirichletBounds
import Sechstmoment.Zeta.DirichletL.DualBound

/-! An actual polynomial boundary estimate for zeta. On `Re(s)=-1/2`,
the Gamma factors cancel exactly after one recurrence and conjugation.
No Stirling or zeta growth estimate is assumed.
-/

namespace Sechstmoment.Source
open Complex Real ComplexConjugate
open scoped Topology
noncomputable section

theorem gammaR_conj_norm (z : ℂ) : ‖Complex.Gammaℝ (conj z)‖ = ‖Complex.Gammaℝ z‖ := by
  have he : conj z/2 = conj (z/2) := by
    apply Complex.ext <;> simp only [Complex.div_ofNat_re,Complex.div_ofNat_im,
      Complex.conj_re,Complex.conj_im]
    ring
  rw [Complex.Gammaℝ_def,Complex.Gammaℝ_def,norm_mul,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,he,Complex.Gamma_conj,norm_conj]
  simp only [Complex.div_ofNat_re,neg_re,Complex.conj_re]

theorem gammaR_ne_zero_on_left_boundary {s : ℂ} (hs : s.re = -1/2) :
    Complex.Gammaℝ s ≠ 0 := by
  intro h
  obtain ⟨n,hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
  have hr := congrArg Complex.re hn
  norm_num only [Complex.neg_re,Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,
    Complex.natCast_re,Complex.natCast_im,mul_zero,zero_sub,sub_zero,hs] at hr
  by_cases hn0 : n = 0
  · norm_num [hn0] at hr
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
    linarith

theorem riemannZeta_norm_left_boundary {s : ℂ} (hs : s.re = -1/2) :
    ‖riemannZeta s‖ = ‖s‖/(2*Real.pi)*‖riemannZeta (1-s)‖ := by
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have ht0 : 1-s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [sub_re,one_re,zero_re,hs] at hr
    norm_num at hr
  have hΓ := gammaR_ne_zero_on_left_boundary hs
  have hΓt : Complex.Gammaℝ (1-s) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by simp only [sub_re,one_re,hs]; norm_num)
  have hc : completedRiemannZeta (1-s) = Complex.Gammaℝ (1-s)*riemannZeta (1-s) := by
    rw [riemannZeta_def_of_ne_zero ht0]
    field_simp
  have hconj : 1-s = conj (s+2) := by
    apply Complex.ext <;> simp only [sub_re,one_re,conj_re,add_re,re_ofNat,
      sub_im,one_im,conj_im,add_im,im_ofNat]
    · linarith
    · ring
  have hnorm : ‖Complex.Gammaℝ (1-s)‖ = ‖Complex.Gammaℝ s‖*‖s‖/(2*Real.pi) := by
    rw [hconj,gammaR_conj_norm,Complex.Gammaℝ_add_two hs0,norm_div,norm_div,norm_mul]
    simp
    ring
  rw [riemannZeta_def_of_ne_zero hs0,← completedRiemannZeta_one_sub,hc,norm_div,norm_mul,hnorm]
  field_simp

theorem riemannZeta_left_boundary_bound {s : ℂ} (hs : s.re = -1/2) :
    ‖riemannZeta s‖ ≤ zetaDirichletMajorant (3/2)*‖s‖/(2*Real.pi) := by
  rw [riemannZeta_norm_left_boundary hs]
  have h := riemannZeta_norm_le_dirichlet (s := 1-s) (b := 3/2) (by norm_num)
    (by simp only [sub_re,one_re,hs]; norm_num)
  calc
    _ ≤ ‖s‖/(2*Real.pi)*zetaDirichletMajorant (3/2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

end
end Sechstmoment.Source
