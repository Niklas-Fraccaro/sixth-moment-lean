import Mathlib.Analysis.Calculus.Deriv.Star
import SixthMoment.Analysis.Complex.RealDerivatives
import SixthMoment.Zeta.Chi.Basic

namespace SixthMoment
open Complex Filter Metric Set
open scoped ComplexConjugate Topology
noncomputable section
set_option maxHeartbeats 0

def d06ComplexChiFrequency (s : ℂ) : ℂ := - (deriv zetaChi s / zetaChi s)

def d06ChiFrequency (t : ℝ) : ℝ := (d06ComplexChiFrequency (criticalLinePoint t)).re

theorem d06CriticalChi_hasDerivAt (t : ℝ) :
    HasDerivAt criticalChi (deriv zetaChi (criticalLinePoint t) * I) t := by
  have ha : AnalyticAt ℂ zetaChi (criticalLinePoint t) :=
    zetaChi_analyticOnNhd_strip _ (by norm_num [criticalLinePoint_re])
  have hp : HasDerivAt (fun z : ℂ => (1/2 : ℂ)+z*I) I (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).mul_const I).const_add (1/2 : ℂ)
  have hh := (ha.differentiableAt.hasDerivAt.comp (t : ℂ) hp).comp_ofReal
  change HasDerivAt criticalChi (deriv zetaChi (criticalLinePoint t)*I) t at hh
  exact hh

theorem d06ComplexChiFrequency_criticalLine_real (t : ℝ) :
    d06ComplexChiFrequency (criticalLinePoint t) = (d06ChiFrequency t : ℂ) := by
  let c := criticalChi t
  let q := deriv zetaChi (criticalLinePoint t) / c
  have hc : c ≠ 0 := criticalChi_ne_zero t
  have hq : deriv zetaChi (criticalLinePoint t) * I = q*c*I := by
    dsimp [q]
    field_simp
  have h := d06CriticalChi_hasDerivAt t
  have hprod := h.mul h.star
  have he : (fun y : ℝ => criticalChi y * star (criticalChi y)) = fun _ => (1 : ℂ) :=
    funext criticalChi_mul_star
  have hz := hprod.deriv
  change deriv (fun y : ℝ => criticalChi y * star (criticalChi y)) t = _ at hz
  rw [he, deriv_const] at hz
  rw [hq] at hz
  have hcc : c * star c = 1 := criticalChi_mul_star t
  have hz' : I * (q - star q) = 0 := by
    have heq : q*c*I*star c + c*star (q*c*I) = I*(q-star q) := by
      simp only [star_mul, show star I = -I from conj_I]
      calc
        _ = I*(q-star q)*(c*star c) := by ring
        _ = _ := by rw [hcc, mul_one]
    exact heq.symm.trans hz.symm
  have hsame : q = star q := sub_eq_zero.mp ((mul_eq_zero.mp hz').resolve_left I_ne_zero)
  have him : q.im = 0 := by
    have hh := congrArg Complex.im hsame
    simp only [star_def, conj_im] at hh
    linarith
  apply Complex.ext
  · rfl
  · simp only [d06ComplexChiFrequency, neg_im, Complex.ofReal_im]
    change -q.im = 0
    rw [him, neg_zero]

theorem d06CriticalChiInv_hasDerivAt (t : ℝ) :
    HasDerivAt (fun y : ℝ => (criticalChi y)⁻¹)
      (I * (d06ChiFrequency t : ℂ) * (criticalChi t)⁻¹) t := by
  have hh := (d06CriticalChi_hasDerivAt t).inv (criticalChi_ne_zero t)
  convert hh using 1
  rw [← d06ComplexChiFrequency_criticalLine_real]
  unfold d06ComplexChiFrequency
  rw [zetaChi_criticalLinePoint]
  field_simp

end
end SixthMoment
