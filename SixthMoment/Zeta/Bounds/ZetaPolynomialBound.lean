import Mathlib.Analysis.Complex.PhragmenLindelof
import SixthMoment.Zeta.Bounds.ZetaStripGrowth


namespace SixthMoment.Source
open Complex Real Filter Set
open scoped Topology
noncomputable section

def zetaPolynomialAux (s : ℂ) : ℂ := polarRegularizedZeta s/(s+2)^2

theorem zetaPolynomialAux_norm {s : ℂ} (hs : s ≠ 1) :
    ‖zetaPolynomialAux s‖ = ‖s-1‖*‖riemannZeta s‖/‖s+2‖^2 := by
  rw [zetaPolynomialAux,polarRegularizedZeta_of_ne_one hs,norm_div,norm_mul,norm_pow]

private theorem shift_norm_geometry {s : ℂ} (hs : -1/2 ≤ s.re) :
    1 ≤ ‖s+2‖ ∧ ‖s-1‖ ≤ ‖s+2‖+3 ∧ ‖s‖ ≤ ‖s+2‖+2 := by
  refine ⟨?_,?_,?_⟩
  · have h := Complex.re_le_norm (s+2)
    simp only [add_re,re_ofNat] at h
    linarith
  · have h := norm_sub_le (s+2) (3 : ℂ)
    rw [show s+2-3 = s-1 by ring] at h
    simpa using h
  · have h := norm_sub_le (s+2) (2 : ℂ)
    rw [add_sub_cancel_right] at h
    simpa using h

theorem zetaPolynomialAux_norm_le_zeta {s : ℂ} (hs : -1/2 ≤ s.re) (hs1 : s ≠ 1) :
    ‖zetaPolynomialAux s‖ ≤ 4*‖riemannZeta s‖ := by
  obtain ⟨hR,hS,_⟩ := shift_norm_geometry hs
  have hden : 0 < ‖s+2‖^2 := by positivity
  have hgeom : ‖s-1‖ ≤ 4*‖s+2‖^2 := by nlinarith [sq_nonneg (‖s+2‖-1)]
  rw [zetaPolynomialAux_norm hs1,div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_right hgeom (norm_nonneg (riemannZeta s))]

theorem zetaPolynomialAux_left_boundary {s : ℂ} (hs : s.re = -1/2) :
    ‖zetaPolynomialAux s‖ ≤ 12*zetaDirichletMajorant (3/2) := by
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  obtain ⟨hR,hS,hT⟩ := shift_norm_geometry hs.ge
  have hden : 0 < ‖s+2‖^2 := by positivity
  have hgeom : ‖s-1‖*‖s‖/‖s+2‖^2 ≤ 12 := by
    rw [div_le_iff₀ hden]
    have h := mul_le_mul hS hT (norm_nonneg s) (by positivity : 0 ≤ ‖s+2‖+3)
    nlinarith [sq_nonneg (‖s+2‖-1)]
  have hZ := zetaDirichletMajorant_nonneg (3/2)
  calc
    _ = ‖s-1‖*‖riemannZeta s‖/‖s+2‖^2 := zetaPolynomialAux_norm hs1
    _ ≤ ‖s-1‖*(zetaDirichletMajorant (3/2)*‖s‖/(2*Real.pi))/‖s+2‖^2 := by
      gcongr
      exact riemannZeta_left_boundary_bound hs
    _ = (zetaDirichletMajorant (3/2)/(2*Real.pi))*(‖s-1‖*‖s‖/‖s+2‖^2) := by ring
    _ ≤ (zetaDirichletMajorant (3/2)/(2*Real.pi))*12 :=
      mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ 12*zetaDirichletMajorant (3/2) := by
      have h := div_le_self hZ (show 1 ≤ 2*Real.pi by linarith [Real.two_le_pi])
      nlinarith

theorem zetaPolynomialAux_right_boundary {s : ℂ} (hs : s.re = 3/2) :
    ‖zetaPolynomialAux s‖ ≤ 12*zetaDirichletMajorant (3/2) := by
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at hs
  have hZ := zetaDirichletMajorant_nonneg (3/2)
  calc
    _ ≤ 4*‖riemannZeta s‖ := zetaPolynomialAux_norm_le_zeta (by linarith) hs1
    _ ≤ 4*zetaDirichletMajorant (3/2) := by
      gcongr
      exact riemannZeta_norm_le_dirichlet (by norm_num) hs.ge
    _ ≤ _ := by linarith

theorem zetaPolynomialAux_diffContOnCl :
    DiffContOnCl ℂ zetaPolynomialAux (Complex.re ⁻¹' Ioo (-1/2 : ℝ) (3/2)) := by
  have hcl : closure (Complex.re ⁻¹' Ioo (-1/2 : ℝ) (3/2)) ⊆
      Complex.re ⁻¹' Icc (-1/2 : ℝ) (3/2) :=
    closure_minimal (fun _ h => ⟨h.1.le,h.2.le⟩) (isClosed_Icc.preimage Complex.continuous_re)
  apply DifferentiableOn.diffContOnCl
  intro s hs
  have hR := (shift_norm_geometry (hcl hs).1).1
  have hz : s+2 ≠ 0 := by intro h; norm_num [h] at hR
  exact ((polarRegularizedZeta_differentiable s).div
    ((differentiableAt_id.add_const 2).pow 2) (pow_ne_zero 2 hz)).differentiableWithinAt

theorem zetaPolynomialAux_bounded_on_strip :
    ∀ s : ℂ, s.re ∈ Icc (-1/2 : ℝ) (3/2) →
      ‖zetaPolynomialAux s‖ ≤ 12*zetaDirichletMajorant (3/2) := by
  obtain ⟨C,hC,hgrowth⟩ := riemannZeta_exponential_crossing_strip
  have hO : zetaPolynomialAux =O[comap (abs ∘ Complex.im) atTop ⊓
      𝓟 (Complex.re ⁻¹' Ioo (-1/2 : ℝ) (3/2))]
      (fun s : ℂ => Real.exp (Real.pi*Real.exp ((1/2)*|s.im|))) := by
    apply Asymptotics.IsBigO.of_bound (4*C)
    simp only [eventually_inf_principal,eventually_comap,Function.comp_apply]
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy s hsy hs
    have ht : 1 ≤ |s.im| := hsy ▸ hy
    have hs1 : s ≠ 1 := by intro h; norm_num [h] at ht
    have he : Real.exp (Real.pi*|s.im|/2) ≤
        Real.exp (Real.pi*Real.exp ((1/2)*|s.im|)) := by
      apply Real.exp_le_exp.mpr
      have h := Real.add_one_le_exp ((1/2)*|s.im|)
      nlinarith [Real.pi_pos]
    calc
      _ ≤ 4*‖riemannZeta s‖ := zetaPolynomialAux_norm_le_zeta hs.1.le hs1
      _ ≤ 4*(C*Real.exp (Real.pi*|s.im|/2)) :=
        mul_le_mul_of_nonneg_left (hgrowth s ⟨hs.1.le,hs.2.le⟩ ht) (by norm_num)
      _ ≤ _ := by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le,← mul_assoc]
        exact mul_le_mul_of_nonneg_left he (by positivity)
  intro s hs
  exact PhragmenLindelof.vertical_strip zetaPolynomialAux_diffContOnCl
    ⟨1/2,by norm_num; linarith [Real.two_le_pi],Real.pi,hO⟩
    (fun _ h => zetaPolynomialAux_left_boundary h)
    (fun _ h => zetaPolynomialAux_right_boundary h) hs.1 hs.2

theorem polarRegularizedZeta_polynomial_crossing_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (-1/2 : ℝ) (3/2) →
      ‖polarRegularizedZeta s‖ ≤ C*(1+|s.im|)^2 := by
  let B := 12*zetaDirichletMajorant (3/2)
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (zetaDirichletMajorant_nonneg (3/2))
  refine ⟨16*B+1,by positivity,?_⟩
  intro s hs
  have hR := (shift_norm_geometry hs.1).1
  have hden : 0 < ‖s+2‖^2 := by positivity
  have haux := zetaPolynomialAux_bounded_on_strip s hs
  rw [zetaPolynomialAux,norm_div,norm_pow,div_le_iff₀ hden] at haux
  have hheight : ‖s+2‖ ≤ 4*(1+|s.im|) := by
    have h := Complex.norm_le_abs_re_add_abs_im (s+2)
    simp only [add_re,re_ofNat,add_im,im_ofNat,add_zero] at h
    rw [abs_of_nonneg (by linarith [hs.1])] at h
    linarith [hs.2,abs_nonneg s.im]
  have hsq : ‖s+2‖^2 ≤ 16*(1+|s.im|)^2 := by nlinarith [norm_nonneg (s+2)]
  have hprod := mul_le_mul_of_nonneg_left hsq hB
  change ‖polarRegularizedZeta s‖ ≤ B*‖s+2‖^2 at haux
  nlinarith [sq_nonneg (1+|s.im|)]

theorem riemannZeta_polynomial_crossing_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (-1/2 : ℝ) (3/2) → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C*(1+|s.im|)^2 := by
  obtain ⟨C,hC,hbound⟩ := polarRegularizedZeta_polynomial_crossing_strip
  refine ⟨C,hC,?_⟩
  intro s hs ht
  have hs1 : s ≠ 1 := by intro h; norm_num [h] at ht
  have hnorm : 1 ≤ ‖s-1‖ := ht.trans (by simpa using Complex.abs_im_le_norm (s-1))
  have h := hbound s hs
  rw [polarRegularizedZeta_of_ne_one hs1,norm_mul] at h
  exact (le_mul_of_one_le_left (norm_nonneg _) hnorm).trans h

theorem riemannZeta_polynomial_critical_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc (1/2 : ℝ) (3/4) →
      ‖riemannZeta s‖ ≤ C*(1+|s.im|)^2 := by
  let B := 12*zetaDirichletMajorant (3/2)
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (zetaDirichletMajorant_nonneg (3/2))
  refine ⟨36*B+1,by positivity,?_⟩
  intro s hs
  have hs1 : s ≠ 1 := by intro h; have hr := congrArg Complex.re h; simp at hr; linarith [hs.2]
  have hR := (shift_norm_geometry (by linarith [hs.1] : -1/2 ≤ s.re)).1
  have hden : 0 < ‖s+2‖^2 := by positivity
  have haux := zetaPolynomialAux_bounded_on_strip s ⟨by linarith [hs.1],by linarith [hs.2]⟩
  rw [zetaPolynomialAux_norm hs1,div_le_iff₀ hden] at haux
  have hdist : 1/4 ≤ ‖s-1‖ := by
    have h := Complex.abs_re_le_norm (s-1)
    simp only [sub_re,one_re] at h
    rw [abs_of_nonpos (by linarith [hs.2])] at h
    linarith [hs.2]
  have hheight : ‖s+2‖ ≤ 3*(1+|s.im|) := by
    have h := Complex.norm_le_abs_re_add_abs_im (s+2)
    simp only [add_re,re_ofNat,add_im,im_ofNat,add_zero] at h
    rw [abs_of_nonneg (by linarith [hs.1])] at h
    linarith [hs.2,abs_nonneg s.im]
  have hsq : ‖s+2‖^2 ≤ 9*(1+|s.im|)^2 := by nlinarith [norm_nonneg (s+2)]
  have hprod := mul_le_mul_of_nonneg_left hsq hB
  have hsmall := mul_le_mul_of_nonneg_right hdist (norm_nonneg (riemannZeta s))
  change ‖s-1‖*‖riemannZeta s‖ ≤ B*‖s+2‖^2 at haux
  nlinarith [sq_nonneg (1+|s.im|)]

end
end SixthMoment.Source
