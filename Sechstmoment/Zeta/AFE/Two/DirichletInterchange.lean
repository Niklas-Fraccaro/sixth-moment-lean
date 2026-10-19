import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-! Exact twofold Dirichlet-series / vertical-integral interchange.  Absolute
summability and the domination are derived from positive real parts. -/
namespace Sechstmoment
open Complex Real MeasureTheory Filter
open scoped BigOperators
noncomputable section

def d02PairDirichletKernel (s r : ℂ) (n : ℕ × ℕ) (v : ℝ) : ℂ :=
  (1/(n.1+1:ℂ)^(s+1+(v:ℂ)*I)) * (1/(n.2+1:ℂ)^(r+1+(v:ℂ)*I))

def d02PairDirichletMass (s r : ℂ) (n : ℕ × ℕ) : ℝ :=
  (n.1+1:ℝ)^(-(s.re+1)) * (n.2+1:ℝ)^(-(r.re+1))

theorem d02PairDirichletKernel_norm (s r : ℂ) (n : ℕ × ℕ) (v : ℝ) :
    ‖d02PairDirichletKernel s r n v‖ = d02PairDirichletMass s r n := by
  unfold d02PairDirichletKernel d02PairDirichletMass
  simp only [norm_mul, norm_div, norm_one]
  rw [show (n.1+1:ℂ)=((n.1+1:ℝ):ℂ) by push_cast; rfl,
    show (n.2+1:ℂ)=((n.2+1:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (n.1+1:ℝ)),
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < (n.2+1:ℝ))]
  simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
    I_im, zero_mul, sub_self, add_zero]
  rw [Real.rpow_neg (by positivity : (0:ℝ)≤n.1+1),
    Real.rpow_neg (by positivity : (0:ℝ)≤n.2+1)]
  simp only [one_div]

theorem d02PairDirichletMass_summable {s r : ℂ}
    (hs : 0 < s.re) (hr : 0 < r.re) : Summable (d02PairDirichletMass s r) := by
  have hsp : Summable (fun n : ℕ => (n+1:ℝ)^(-(s.re+1))) := by
    convert ((Real.summable_one_div_nat_add_rpow 1 (s.re+1)).mpr (by linarith)) using 1
    funext n
    rw [abs_of_pos (by positivity : (0:ℝ)<n+1),
      Real.rpow_neg (by positivity : (0:ℝ)≤n+1)]
    simp only [one_div]
  have hrp : Summable (fun n : ℕ => (n+1:ℝ)^(-(r.re+1))) := by
    convert ((Real.summable_one_div_nat_add_rpow 1 (r.re+1)).mpr (by linarith)) using 1
    funext n
    rw [abs_of_pos (by positivity : (0:ℝ)<n+1),
      Real.rpow_neg (by positivity : (0:ℝ)≤n+1)]
    simp only [one_div]
  exact hsp.mul_of_nonneg hrp (fun _ => by positivity) (fun _ => by positivity)

theorem d02PairDirichletKernel_tsum {s r : ℂ}
    (hs : 0 < s.re) (hr : 0 < r.re) (v : ℝ) :
    (∑' n : ℕ × ℕ, d02PairDirichletKernel s r n v) =
      riemannZeta (s+1+(v:ℂ)*I) * riemannZeta (r+1+(v:ℂ)*I) := by
  have hsa : 1 < (s+1+(v:ℂ)*I).re := by simpa using (by linarith : 1<s.re+1)
  have hra : 1 < (r+1+(v:ℂ)*I).re := by simpa using (by linarith : 1<r.re+1)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hsa,
    zeta_eq_tsum_one_div_nat_add_one_cpow hra]
  unfold d02PairDirichletKernel
  symm
  apply tsum_mul_tsum_of_summable_norm
  · have hsp := ((Real.summable_one_div_nat_add_rpow 1 (s.re+1)).mpr (by linarith))
    convert hsp using 1
    funext n
    rw [norm_div, norm_one,
      show (n+1:ℂ)=((n+1:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
      abs_of_pos (by positivity : (0:ℝ)<n+1)]
    simp
  · have hrp := ((Real.summable_one_div_nat_add_rpow 1 (r.re+1)).mpr (by linarith))
    convert hrp using 1
    funext n
    rw [norm_div, norm_one,
      show (n+1:ℂ)=((n+1:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
      abs_of_pos (by positivity : (0:ℝ)<n+1)]
    simp

theorem d02PairDirichletKernel_continuous (s r : ℂ) (n : ℕ × ℕ) :
    Continuous (d02PairDirichletKernel s r n) := by
  unfold d02PairDirichletKernel
  have h1 : (n.1+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n.1
  have h2 : (n.2+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero n.2
  apply Continuous.mul
  · exact continuous_const.div
      (Continuous.const_cpow (by fun_prop) (Or.inl h1))
      (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl h1))
  · exact continuous_const.div
      (Continuous.const_cpow (by fun_prop) (Or.inl h2))
      (fun _ => Complex.cpow_ne_zero_iff.mpr (Or.inl h2))

/-- Literal Fubini for both unrestricted positive Dirichlet indices. -/
theorem d02PairDirichlet_integral_interchange {s r : ℂ}
    (hs : 0 < s.re) (hr : 0 < r.re) (F : ℝ → ℂ) (hF : Integrable F) :
    (∑' n : ℕ × ℕ, ∫ v : ℝ, F v * d02PairDirichletKernel s r n v) =
      ∫ v : ℝ, F v * riemannZeta (s+1+(v:ℂ)*I) *
        riemannZeta (r+1+(v:ℂ)*I) := by
  have hFI (n : ℕ × ℕ) : Integrable (fun v => F v*d02PairDirichletKernel s r n v) := by
    apply (hF.norm.mul_const (d02PairDirichletMass s r n)).mono'
      (hF.aestronglyMeasurable.mul (d02PairDirichletKernel_continuous s r n).aestronglyMeasurable)
    exact Eventually.of_forall fun v => by
      change ‖F v*d02PairDirichletKernel s r n v‖≤‖F v‖*d02PairDirichletMass s r n
      rw [norm_mul, d02PairDirichletKernel_norm]
  have he (n : ℕ × ℕ) : (∫ v : ℝ, ‖F v*d02PairDirichletKernel s r n v‖) =
      (∫ v : ℝ, ‖F v‖) * d02PairDirichletMass s r n := by
    simp_rw [norm_mul, d02PairDirichletKernel_norm]
    exact integral_mul_const _ _
  rw [integral_tsum_of_summable_integral_norm hFI (by
    simp_rw [he]
    exact (d02PairDirichletMass_summable hs hr).mul_left _)]
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    change (∑' n : ℕ × ℕ,F v*d02PairDirichletKernel s r n v) =
      F v*riemannZeta (s+1+(v:ℂ)*I)*riemannZeta (r+1+(v:ℂ)*I)
    rw [tsum_mul_left, d02PairDirichletKernel_tsum hs hr]
    ring

end
end Sechstmoment
