import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import SixthMoment.Numerator.V.Arithmetic.TimeWeightFamily
import SixthMoment.Numerator.V.Chi.GlobalTime
import SixthMoment.Numerator.V.Chi.WideWindow


namespace SixthMoment.Source
open Complex Real Set MeasureTheory
noncomputable section

def noDPChiTimeTransform (w : ℝ → ℂ) (T c : ℝ) (u : ℂ) (r : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*(∫ t : ℝ,
    (r:ℂ)^(-((c:ℂ)+(t:ℂ)*I))*zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)*w (t/T))

theorem noDPChiTimeTransform_shift (w : ℝ → ℂ) (T c : ℝ) (u : ℂ)
    {r : ℝ} (hr : 0 < r) :
    noDPChiTimeTransform w T c u r =
      (r:ℂ)^(-u)*(1/(2*Real.pi):ℂ)*(∫ v : ℝ,
        (r:ℂ)^(-(((c-u.re:ℝ):ℂ)+(v:ℂ)*I))*
          zetaChi (1-(((c-u.re:ℝ):ℂ)+(v:ℂ)*I))*w ((v+u.im)/T)) := by
  let F : ℝ → ℂ := fun t =>
    (r:ℂ)^(-((c:ℂ)+(t:ℂ)*I))*zetaChi (1-((c:ℂ)+(t:ℂ)*I)+u)*w (t/T)
  let G : ℝ → ℂ := fun v =>
    (r:ℂ)^(-(((c-u.re:ℝ):ℂ)+(v:ℂ)*I))*
      zetaChi (1-(((c-u.re:ℝ):ℂ)+(v:ℂ)*I))*w ((v+u.im)/T)
  have hrC : (r:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hpoint (v : ℝ) : F (v+u.im) = (r:ℂ)^(-u)*G v := by
    have hs : (c:ℂ)+((v+u.im:ℝ):ℂ)*I = ((c-u.re:ℝ):ℂ)+(v:ℂ)*I+u := by
      apply Complex.ext <;> simp
    dsimp only [F,G]
    rw [hs,show 1-(((c-u.re:ℝ):ℂ)+(v:ℂ)*I+u)+u =
      1-(((c-u.re:ℝ):ℂ)+(v:ℂ)*I) by ring,neg_add,
      Complex.cpow_add _ _ hrC]
    ring
  change (1/(2*Real.pi):ℂ)*(∫ t : ℝ, F t) =
    (r:ℂ)^(-u)*(1/(2*Real.pi):ℂ)*(∫ v : ℝ, G v)
  rw [← integral_add_right_eq_self (μ := volume) F u.im]
  simp_rw [hpoint]
  rw [integral_const_mul]
  ring

theorem noDPTimeWeight_frequency_value (w : ℝ → ℂ)
    {T r : ℝ} (hT : 0 < T) (hr : 0 < r) (u : ℂ) :
    noDPTimeWeight w T u (2*Real.pi*r/T) =
      (r:ℂ)^(-u)*w (2*Real.pi*r/T) := by
  have hx : 0 < 2*Real.pi*r/T := by positivity
  have he : T*(2*Real.pi*r/T)/(2*Real.pi) = r := by
    rw [← mul_div_assoc,mul_div_cancel_left₀ (2*Real.pi*r) hT.ne',
      mul_div_cancel_left₀ r (by positivity : 2*Real.pi ≠ 0)]
  rw [noDPTimeWeight_eq_scaled_power w hT hx u]
  unfold chiShiftLeadingPhase
  rw [he]
  ring

end
end SixthMoment.Source
