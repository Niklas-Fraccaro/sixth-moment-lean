import SixthMoment.Denominator.Unbalanced.MomentDefinitions
import SixthMoment.Zeta.AFE.OneSided.Mellin

namespace SixthMoment
open Complex Real MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section

def d04OneSidedMellinIntegrand (X : ℝ) (s r z : ℂ) : ℂ :=
  Complex.Gamma z*(X : ℂ)^z*riemannZeta (s+z)*riemannZeta (r+z)

def d04OneSidedMellinIntegral (X : ℝ) (s r : ℂ) : ℂ :=
  (1/(2*Real.pi) : ℂ)*∫ v : ℝ,
    d04OneSidedMellinIntegrand X s r (d04MellinLine v)

theorem d04GammaMellin_scaled_integrable {X : ℝ} (hX : 0<X) :
    Integrable (fun v : ℝ => Complex.Gamma (d04MellinLine v)*(X : ℂ)^(d04MellinLine v)) := by
  have hnorm (v : ℝ) : ‖(X : ℂ)^(d04MellinLine v)‖=X^2 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, d04MellinLine_re]
    norm_cast
  apply (d04Gamma_line_two_integrable.norm.mul_const (X^2)).mono'
  · apply d04Gamma_line_two_integrable.aestronglyMeasurable.mul
    exact (Continuous.const_cpow (by unfold d04MellinLine; fun_prop)
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))).aestronglyMeasurable
  · exact Eventually.of_forall (fun v => by rw [norm_mul, hnorm])

theorem d04OneSidedMellinKernel_identity {X : ℝ} (hX : 0<X)
    (s r : ℂ) (n : ℕ×ℕ) (v : ℝ) :
    Complex.Gamma (d04MellinLine v)*(X : ℂ)^(d04MellinLine v)*
      d02PairDirichletKernel (s+1) (r+1) n v =
    ((n.1+1 : ℂ)^(-s)*(n.2+1 : ℂ)^(-r))*
      (((n.1+1 : ℝ)*(n.2+1 : ℝ)/X : ℝ) : ℂ)^(-d04MellinLine v)*
      Complex.Gamma (d04MellinLine v) := by
  let z := d04MellinLine v
  have hn1 : (n.1+1 : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n.1
  have hn2 : (n.2+1 : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n.2
  have he1 : s+1+1+(v : ℂ)*I=s+z := by dsimp [z, d04MellinLine]; ring
  have he2 : r+1+1+(v : ℂ)*I=r+z := by dsimp [z, d04MellinLine]; ring
  unfold d02PairDirichletKernel
  rw [he1, he2, one_div, one_div, ← Complex.cpow_neg, ← Complex.cpow_neg]
  rw [show -(s+z)=-s+-z by ring, show -(r+z)=-r+-z by ring,
    Complex.cpow_add _ _ hn1, Complex.cpow_add _ _ hn2]
  rw [Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg (by positivity) hX.le, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    Complex.cpow_neg (X : ℂ)]
  simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    div_inv_eq_mul]
  ring

theorem d04OneSidedMellin_term_integral {X : ℝ} (hX : 0<X)
    (s r : ℂ) (n : ℕ×ℕ) :
    (1/(2*Real.pi) : ℂ)*∫ v : ℝ,
      Complex.Gamma (d04MellinLine v)*(X : ℂ)^(d04MellinLine v)*
        d02PairDirichletKernel (s+1) (r+1) n v =
      d04OneSidedRawSummand X s r n := by
  simp_rw [d04OneSidedMellinKernel_identity hX s r n]
  rw [show (fun v : ℝ => ((n.1+1 : ℂ)^(-s)*(n.2+1 : ℂ)^(-r))*
      (((n.1+1 : ℝ)*(n.2+1 : ℝ)/X : ℝ) : ℂ)^(-d04MellinLine v)*
      Complex.Gamma (d04MellinLine v)) =
    (fun v : ℝ => ((n.1+1 : ℂ)^(-s)*(n.2+1 : ℂ)^(-r))*
      ((((n.1+1 : ℝ)*(n.2+1 : ℝ)/X : ℝ) : ℂ)^(-d04MellinLine v)*
        Complex.Gamma (d04MellinLine v))) by funext v; ring]
  rw [integral_const_mul]
  have hx : 0<((n.1+1 : ℝ)*(n.2+1 : ℝ)/X) := by positivity
  have hi := d04GammaMellin_exponential hx
  unfold d04OneSidedRawSummand
  rw [show (1/(2*Real.pi) : ℂ)*
    (((n.1+1 : ℂ)^(-s)*(n.2+1 : ℂ)^(-r))*
      ∫ v : ℝ, (((n.1+1 : ℝ)*(n.2+1 : ℝ)/X : ℝ) : ℂ)^(-d04MellinLine v)*
        Complex.Gamma (d04MellinLine v)) =
    ((n.1+1 : ℂ)^(-s)*(n.2+1 : ℂ)^(-r))*
      ((1/(2*Real.pi) : ℂ)*∫ v : ℝ,
        (((n.1+1 : ℝ)*(n.2+1 : ℝ)/X : ℝ) : ℂ)^(-d04MellinLine v)*
          Complex.Gamma (d04MellinLine v)) by ring, hi]
  congr 2
  ring

theorem d04OneSidedRawSeries_eq_mellin {X : ℝ} (hX : 0<X)
    {s r : ℂ} (hs : -1<s.re) (hr : -1<r.re) :
    d04OneSidedRawSeries X s r=d04OneSidedMellinIntegral X s r := by
  have hs' : 0<(s+1).re := by simp only [add_re, one_re]; linarith
  have hr' : 0<(r+1).re := by simp only [add_re, one_re]; linarith
  have h := d02PairDirichlet_integral_interchange hs' hr'
    (fun v => Complex.Gamma (d04MellinLine v)*(X : ℂ)^(d04MellinLine v))
    (d04GammaMellin_scaled_integrable hX)
  unfold d04OneSidedRawSeries d04OneSidedMellinIntegral d04OneSidedMellinIntegrand
  simp_rw [← d04OneSidedMellin_term_integral hX s r]
  rw [tsum_mul_left, h]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  congr 2 <;> unfold d04MellinLine <;> ring

end
end SixthMoment
