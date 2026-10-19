import Sechstmoment.Analysis.Complex.PositivePowers
import Sechstmoment.Numerator.U.Replacement.VStar.XMellinAbsoluteMass
import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.Measurability

/-! Absolute positive-x/time Fubini for the literal VStar factor. The time
profile is compactly supported away from zero; no exchange is assumed. -/
namespace Sechstmoment.Source
open Complex Real Set MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 700000

private theorem mainTimePower_integrable {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (z : ℂ) :
    Integrable (fun t : ℝ => Φ t*(t:ℂ)^z) := by
  have hc : ContDiff ℝ ∞ (Sechstmoment.a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^z)) :=
    Sechstmoment.a03_profile_product_contDiff hΦ (fun t ht =>
      Sechstmoment.positive_cpow_contDiffAt z (zero_lt_one.trans_le (hSupp ht).1))
  have hk : HasCompactSupport (Sechstmoment.a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^z)) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      ((Sechstmoment.a03_profile_product_tsupport _ _).trans hSupp)
  exact hc.continuous.integrable_of_hasCompactSupport hk

def a03VStarSquareTimeDensity (G : ℂ→ℂ) (Φ : ℝ→ℂ)
    (Y : ℝ) (q s : ℂ) (x t : ℝ) : ℂ :=
  (x:ℂ)^(q-1)*bblrVStar G (x^2/(Y^2*t^2))*Φ t*(t:ℂ)^(-s)

theorem a03VStarSquareTimeDensity_joint_integrable {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {Y : ℝ} (hY : 0<Y) {q : ℂ} (hq : 0<q.re) (s : ℂ)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    Integrable (Function.uncurry (a03VStarSquareTimeDensity G Φ Y q s))
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hmG : Measurable G := (continuousOn_univ.mp hG.1.continuousOn).measurable
  have hV := a03VStar_measurable G hmG
  have hm : Measurable (Function.uncurry (a03VStarSquareTimeDensity G Φ Y q s)) := by
    have hx : Measurable (fun p : ℝ×ℝ => (p.1:ℂ)^(q-1)) :=
      a03MeasurableCPow (Complex.measurable_ofReal.comp measurable_fst) measurable_const
    have ht : Measurable (fun p : ℝ×ℝ => (p.2:ℂ)^(-s)) :=
      a03MeasurableCPow (Complex.measurable_ofReal.comp measurable_snd) measurable_const
    exact ((hx.mul (hV.comp (by fun_prop))).mul (hΦ.continuous.measurable.comp measurable_snd)).mul ht
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · apply ae_of_all
    intro t
    by_cases ht : Φ t=0
    · simp only [Function.uncurry,a03VStarSquareTimeDensity,ht,mul_zero,zero_mul]
      exact integrable_zero _ _ _
    · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
      have hi := (bblrVStar_square_scaled_xMellin hq (mul_pos hY htp) G α hG).1
      apply (hi.mul_const (Φ t*(t:ℂ)^(-s))).congr
      apply ae_of_all
      intro x
      unfold Function.uncurry a03VStarSquareTimeDensity
      rw [mul_pow]
      ring
  · let C : ℝ := Y^q.re*a03VStarAbsoluteSquareMass G q.re 1
    have hi := (mainTimePower_integrable hΦ hSupp (q-s)).norm.const_mul C
    apply hi.congr
    apply ae_of_all
    intro t
    change C*‖Φ t*(t:ℂ)^(q-s)‖=
      ∫x : ℝ in Ioi 0,‖a03VStarSquareTimeDensity G Φ Y q s x t‖
    by_cases ht : Φ t=0
    · simp [a03VStarSquareTimeDensity,ht]
    · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
      have hn (x : ℝ) (hx : x∈Ioi (0:ℝ)) :
          ‖a03VStarSquareTimeDensity G Φ Y q s x t‖=
          (‖Φ t‖*t^(-s.re))*(x^(q.re-1)*‖bblrVStar G (x^2/(Y*t)^2)‖) := by
        unfold a03VStarSquareTimeDensity
        rw [norm_mul,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,
          Complex.norm_cpow_eq_rpow_re_of_pos htp]
        simp only [Complex.sub_re,Complex.one_re,Complex.neg_re,mul_pow]
        ring
      rw [setIntegral_congr_fun measurableSet_Ioi hn,integral_const_mul]
      change _=(‖Φ t‖*t^(-s.re))*a03VStarAbsoluteSquareMass G q.re (Y*t)
      rw [a03VStarAbsoluteSquareMass_scale G q.re (mul_pos hY htp),
        Real.mul_rpow hY.le htp.le,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos htp,
        Complex.sub_re]
      have hp : t^(-s.re)*t^q.re=t^(q.re-s.re) := by
        rw [←Real.rpow_add htp]
        congr 1
        ring
      dsimp only [C]
      calc
        _=(Y^q.re*a03VStarAbsoluteSquareMass G q.re 1)*‖Φ t‖*(t^(-s.re)*t^q.re) := by rw [hp]; ring
        _=_ := by ring

theorem a03VStarSquareTimeDensity_x_time_eq {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {Y : ℝ} (hY : 0<Y) {q : ℂ} (hq : 0<q.re) (s : ℂ)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    (∫x : ℝ in Ioi 0,∫t : ℝ,a03VStarSquareTimeDensity G Φ Y q s x t)=
      (Y:ℂ)^q*(2*Real.pi:ℂ)^(-q)*(G (q/2)/q)*
        ∫t : ℝ,Φ t*(t:ℂ)^(q-s) := by
  have hj := a03VStarSquareTimeDensity_joint_integrable hΦ hSupp hY hq s G α hG
  rw [integral_integral_swap hj,←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  by_cases ht : Φ t=0
  · simp [a03VStarSquareTimeDensity,ht]
  · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
    have he := (bblrVStar_square_scaled_xMellin hq (mul_pos hY htp) G α hG).2
    unfold a03VStarSquareTimeDensity
    rw [mul_pow] at he
    rw [show (fun x : ℝ => (x:ℂ)^(q-1)*bblrVStar G (x^2/(Y^2*t^2))*Φ t*(t:ℂ)^(-s))=
      (fun x : ℝ => (Φ t*(t:ℂ)^(-s))*((x:ℂ)^(q-1)*bblrVStar G (x^2/(Y^2*t^2)))) by funext x; ring,
      integral_const_mul,he]
    have hmul : ((Y*t:ℝ):ℂ)^q=(Y:ℂ)^q*(t:ℂ)^q := by
      rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hY.le htp.le]
    have hp : (t:ℂ)^(-s)*(t:ℂ)^q=(t:ℂ)^(q-s) := by
      rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr htp.ne')]
      congr 1
      ring
    rw [hmul]
    calc
      _=(Y:ℂ)^q*(2*Real.pi:ℂ)^(-q)*(G (q/2)/q)*Φ t*((t:ℂ)^(-s)*(t:ℂ)^q) := by ring
      _=_ := by rw [hp]; ring

end
end Sechstmoment.Source
