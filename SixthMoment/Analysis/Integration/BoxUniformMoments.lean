import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.ConditionalProbability
import SixthMoment.Analysis.Integration.BoxMoments


namespace SixthMoment
open MeasureTheory

noncomputable def symmetricUniform (r : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Set.Icc (-(r/2)) (r/2))

theorem symmetricUniform_probability {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (symmetricUniform r) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc, show r/2 - -(r/2) = r by ring]
    exact (ENNReal.ofReal_pos.mpr hr).ne'
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

theorem symmetricUniform_integral {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ) :
    (∫ x, f x ∂symmetricUniform r) =
      (∫ x in -(r/2)..r/2, f x) / r := by
  have h : -(r/2) ≤ r/2 := by linarith
  rw [symmetricUniform, ProbabilityTheory.cond, integral_smul_measure,
    Real.volume_Icc, show r/2 - -(r/2) = r by ring,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hr.le,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

noncomputable def uniformBoxExpectation (r s t : ℝ)
    (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  ∫ x, ∫ y, ∫ z, f x y z ∂symmetricUniform t ∂symmetricUniform s ∂symmetricUniform r

theorem uniformBoxExpectation_eq_box {r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (f : ℝ → ℝ → ℝ → ℝ) :
    uniformBoxExpectation r s t f = boxIntegral r s t f / (r*s*t) := by
  unfold uniformBoxExpectation boxIntegral
  simp_rw [symmetricUniform_integral hr, symmetricUniform_integral hs,
    symmetricUniform_integral ht, div_eq_mul_inv,
    intervalIntegral.integral_mul_const]
  ring

noncomputable def uniformBoxLaw (r s t : ℝ) : Measure (ℝ × (ℝ × ℝ)) :=
  (symmetricUniform r).prod ((symmetricUniform s).prod (symmetricUniform t))

theorem uniformBoxLaw_eq_restrict (r s t : ℝ) :
    uniformBoxLaw r s t =
      ((volume (Set.Icc (-(r/2)) (r/2)))⁻¹ *
        (volume (Set.Icc (-(s/2)) (s/2)))⁻¹ *
        (volume (Set.Icc (-(t/2)) (t/2)))⁻¹) •
      (volume.restrict (Set.Icc (-(r/2)) (r/2) ×ˢ
        (Set.Icc (-(s/2)) (s/2) ×ˢ Set.Icc (-(t/2)) (t/2)))) := by
  simp only [uniformBoxLaw, symmetricUniform, ProbabilityTheory.cond,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    Measure.prod_restrict, ← Measure.volume_eq_prod, mul_assoc, mul_comm]

theorem uniformBoxLaw_integrable_of_continuous {r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t)
    (f : (ℝ × (ℝ × ℝ)) → ℝ) (hf : Continuous f) :
    Integrable f (uniformBoxLaw r s t) := by
  rw [uniformBoxLaw_eq_restrict]
  apply (hf.continuousOn.integrableOn_compact
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).smul_measure
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top
    · rw [Real.volume_Icc, show r/2 - -(r/2) = r by ring]
      exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hr).ne'
    · rw [Real.volume_Icc, show s/2 - -(s/2) = s by ring]
      exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hs).ne'
  · rw [Real.volume_Icc, show t/2 - -(t/2) = t by ring]
    exact ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr ht).ne'

theorem uniformBoxLaw_probability {r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    IsProbabilityMeasure (uniformBoxLaw r s t) := by
  let := symmetricUniform_probability hr
  let := symmetricUniform_probability hs
  let := symmetricUniform_probability ht
  unfold uniformBoxLaw
  infer_instance

theorem uniformBoxLaw_integral {r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Integrable (fun u : ℝ × (ℝ × ℝ) => f u.1 u.2.1 u.2.2)
      (uniformBoxLaw r s t)) :
    (∫ u, f u.1 u.2.1 u.2.2 ∂uniformBoxLaw r s t) =
      boxIntegral r s t f / (r*s*t) := by
  let := symmetricUniform_probability hr
  let := symmetricUniform_probability hs
  let := symmetricUniform_probability ht
  rw [uniformBoxLaw, integral_prod _ hf]
  have he : (∫ x, ∫ u : ℝ × ℝ, f x u.1 u.2
      ∂(symmetricUniform s).prod (symmetricUniform t) ∂symmetricUniform r) =
      uniformBoxExpectation r s t f := by
    apply integral_congr_ae
    filter_upwards [hf.prod_right_ae] with x hx
    exact integral_prod _ hx
  rw [he, uniformBoxExpectation_eq_box hr hs ht]

theorem uniformBoxLaw_integral_of_continuous {r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Continuous (fun u : ℝ × (ℝ × ℝ) => f u.1 u.2.1 u.2.2)) :
    (∫ u, f u.1 u.2.1 u.2.2 ∂uniformBoxLaw r s t) =
      boxIntegral r s t f / (r*s*t) :=
  uniformBoxLaw_integral hr hs ht f
    (uniformBoxLaw_integrable_of_continuous hr hs ht _ hf)

theorem uniformBox_power_0 {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    uniformBoxExpectation r s t (fun x y z => (x+y+z)^0) =
      (1 : ℝ)/1 := by
  rw [uniformBoxExpectation_eq_box hr hs ht, box_power_0]
  field_simp [hr.ne', hs.ne', ht.ne']

theorem uniformBox_power_1 {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    uniformBoxExpectation r s t (fun x y z => (x+y+z)^1) =
      0 := by
  rw [uniformBoxExpectation_eq_box hr hs ht, box_power_1]
  simp

theorem uniformBox_power_2 {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    uniformBoxExpectation r s t (fun x y z => (x+y+z)^2) =
      (1 : ℝ)/12*t^2 +
      (1 : ℝ)/12*s^2 +
      (1 : ℝ)/12*r^2 := by
  rw [uniformBoxExpectation_eq_box hr hs ht, box_power_2]
  field_simp [hr.ne', hs.ne', ht.ne']

theorem uniformBox_power_3 {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    uniformBoxExpectation r s t (fun x y z => (x+y+z)^3) =
      0 := by
  rw [uniformBoxExpectation_eq_box hr hs ht, box_power_3]
  simp

theorem uniformBox_power_4 {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    uniformBoxExpectation r s t (fun x y z => (x+y+z)^4) =
      (1 : ℝ)/80*t^4 +
      (1 : ℝ)/24*s^2*t^2 +
      (1 : ℝ)/80*s^4 +
      (1 : ℝ)/24*r^2*t^2 +
      (1 : ℝ)/24*r^2*s^2 +
      (1 : ℝ)/80*r^4 := by
  rw [uniformBoxExpectation_eq_box hr hs ht, box_power_4]
  field_simp [hr.ne', hs.ne', ht.ne']

theorem uniformBox_power_5 {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    uniformBoxExpectation r s t (fun x y z => (x+y+z)^5) =
      0 := by
  rw [uniformBoxExpectation_eq_box hr hs ht, box_power_5]
  simp

theorem uniformBox_power_6 {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    uniformBoxExpectation r s t (fun x y z => (x+y+z)^6) =
      (1 : ℝ)/448*t^6 +
      (1 : ℝ)/64*s^2*t^4 +
      (1 : ℝ)/64*s^4*t^2 +
      (1 : ℝ)/448*s^6 +
      (1 : ℝ)/64*r^2*t^4 +
      (5 : ℝ)/96*r^2*s^2*t^2 +
      (1 : ℝ)/64*r^2*s^4 +
      (1 : ℝ)/64*r^4*t^2 +
      (1 : ℝ)/64*r^4*s^2 +
      (1 : ℝ)/448*r^6 := by
  rw [uniformBoxExpectation_eq_box hr hs ht, box_power_6]
  field_simp [hr.ne', hs.ne', ht.ne']

theorem uniformBox_power_7 {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    uniformBoxExpectation r s t (fun x y z => (x+y+z)^7) =
      0 := by
  rw [uniformBoxExpectation_eq_box hr hs ht, box_power_7]
  simp

theorem uniformBox_power_8 {r s t : ℝ} (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    uniformBoxExpectation r s t (fun x y z => (x+y+z)^8) =
      (1 : ℝ)/2304*t^8 +
      (1 : ℝ)/192*s^2*t^6 +
      (7 : ℝ)/640*s^4*t^4 +
      (1 : ℝ)/192*s^6*t^2 +
      (1 : ℝ)/2304*s^8 +
      (1 : ℝ)/192*r^2*t^6 +
      (7 : ℝ)/192*r^2*s^2*t^4 +
      (7 : ℝ)/192*r^2*s^4*t^2 +
      (1 : ℝ)/192*r^2*s^6 +
      (7 : ℝ)/640*r^4*t^4 +
      (7 : ℝ)/192*r^4*s^2*t^2 +
      (7 : ℝ)/640*r^4*s^4 +
      (1 : ℝ)/192*r^6*t^2 +
      (1 : ℝ)/192*r^6*s^2 +
      (1 : ℝ)/2304*r^8 := by
  rw [uniformBoxExpectation_eq_box hr hs ht, box_power_8]
  field_simp [hr.ne', hs.ne', ht.ne']

theorem uniformBoxLaw_moment {r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) (k : ℕ) :
    (∫ u : ℝ × (ℝ × ℝ), (u.1+u.2.1+u.2.2)^k ∂uniformBoxLaw r s t) =
      uniformBoxExpectation r s t (fun x y z => (x+y+z)^k) := by
  rw [uniformBoxLaw_integral_of_continuous hr hs ht (fun x y z => (x+y+z)^k) (by fun_prop),
    uniformBoxExpectation_eq_box hr hs ht]

end SixthMoment
