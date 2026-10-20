import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Sechstmoment.Zeta.Moments.AnalyticMomentLinearity


namespace Sechstmoment
open Complex MeasureTheory Set Filter
open scoped Topology

noncomputable section

theorem smoothDyadicWeight_zero_above (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    {x : ℝ} (hx : 2 < x) : Φ x=0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  exact (not_le_of_gt hx) (hΦ.2 hm).2

theorem smoothDyadicWeight_zero_below (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    {x : ℝ} (hx : x < 1) : Φ x=0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  exact (not_le_of_gt hx) (hΦ.2 hm).1

theorem smoothDyadicWeight_zero_two (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Φ 2=0 := by
  have hz : Φ =ᶠ[𝓝[Ioi 2] 2] (fun _ => 0) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact smoothDyadicWeight_zero_above Φ hΦ hx
  have hlim : Tendsto Φ (𝓝[Ioi 2] 2) (𝓝 (Φ 2)) :=
    hΦ.1.continuous.continuousAt.tendsto.mono_left inf_le_left
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hz.symm)

def sharpPrimitive (H : ℝ → ℂ) (x : ℝ) : ℂ := ∫ t : ℝ in 1..x, H t

theorem sharpPrimitive_hasDerivAt (H : ℝ → ℂ) (hH : Continuous H) (x : ℝ) :
    HasDerivAt (sharpPrimitive H) (H x) x := by
  exact intervalIntegral.integral_hasDerivAt_right (hH.intervalIntegrable 1 x)
    hH.stronglyMeasurable.stronglyMeasurableAtFilter hH.continuousAt

theorem sharpPrimitive_continuous (H : ℝ → ℂ) (hH : Continuous H) :
    Continuous (sharpPrimitive H) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (sharpPrimitive_hasDerivAt H hH x).continuousAt

theorem dyadic_partial_summation {T : ℝ} (hT : 1 < T)
    (H : ℝ → ℂ) (hH : Continuous H) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    (∫ t : ℝ, (Φ (t/T) : ℂ)*H t) =
      -(∫ x : ℝ in 1..(2*T), ((deriv Φ (x/T)/T : ℝ) : ℂ)*sharpPrimitive H x) := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hsupport : Function.support (fun t => (Φ (t/T) : ℂ)*H t) ⊆ Ioc 1 (2*T) := by
    intro t ht
    have hφ : Φ (t/T) ≠ 0 := by
      intro hz
      simp [Function.mem_support, hz] at ht
    have harg := hΦ.2 (subset_tsupport Φ (Function.mem_support.mpr hφ))
    constructor
    · have h := (le_div_iff₀ hT0).mp harg.1
      linarith
    · exact (div_le_iff₀ hT0).mp harg.2
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupport]
  have hw (x : ℝ) : HasDerivAt (fun x => (Φ (x/T) : ℂ))
      ((deriv Φ (x/T)/T : ℝ) : ℂ) x := by
    apply HasDerivAt.ofReal_comp
    simpa only [one_div, div_eq_mul_inv, Function.comp_def, id_eq, one_mul] using
      (hΦ.1.differentiable (by simp)).differentiableAt.hasDerivAt.comp x
        ((hasDerivAt_id x).div_const T)
  have hc : Continuous (fun x => (Φ (x/T) : ℂ)) := by
    have := hΦ.1.continuous
    fun_prop
  have hd : Continuous (fun x => ((deriv Φ (x/T)/T : ℝ) : ℂ)) := by
    have h := hΦ.1.continuous_deriv (by simp)
    fun_prop
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hc.continuousOn (sharpPrimitive_continuous H hH).continuousOn
    (fun x _ => hw x) (fun x _ => sharpPrimitive_hasDerivAt H hH x)
    (hd.intervalIntegrable _ _) (hH.intervalIntegrable _ _)]
  have hφend : Φ (2*T/T)=0 := by
    rw [mul_div_cancel_right₀ (2 : ℝ) hT0.ne']
    exact smoothDyadicWeight_zero_two Φ hΦ
  simp [hφend, sharpPrimitive]

theorem dyadic_centered_partial_summation {T : ℝ} (hT : 1 < T)
    (H : ℝ → ℂ) (hH : Continuous H) (M : ℂ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    (∫ t : ℝ, (Φ (t/T) : ℂ)*(H t-M)) =
      -(∫ x : ℝ in 1..(2*T), ((deriv Φ (x/T)/T : ℝ) : ℂ)*
        (sharpPrimitive H x-(x : ℂ)*M)) := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hsupport : Function.support (fun t => (Φ (t/T) : ℂ)*(H t-M)) ⊆ Ioc 1 (2*T) := by
    intro t ht
    have hφ : Φ (t/T) ≠ 0 := by
      intro hz
      simp [Function.mem_support, hz] at ht
    have harg := hΦ.2 (subset_tsupport Φ (Function.mem_support.mpr hφ))
    constructor
    · have h := (le_div_iff₀ hT0).mp harg.1
      linarith
    · exact (div_le_iff₀ hT0).mp harg.2
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupport]
  have hw (x : ℝ) : HasDerivAt (fun x => (Φ (x/T) : ℂ))
      ((deriv Φ (x/T)/T : ℝ) : ℂ) x := by
    apply HasDerivAt.ofReal_comp
    simpa only [one_div, div_eq_mul_inv, Function.comp_def, id_eq, one_mul] using
      (hΦ.1.differentiable (by simp)).differentiableAt.hasDerivAt.comp x
        ((hasDerivAt_id x).div_const T)
  have hv (x : ℝ) : HasDerivAt
      (fun x => sharpPrimitive H x-(x : ℂ)*M) (H x-M) x := by
    simpa only [Pi.sub_def, id_eq, Complex.ofReal_one, one_mul] using (sharpPrimitive_hasDerivAt H hH x).sub
      ((hasDerivAt_id x).ofReal_comp.mul_const M)
  have hc : Continuous (fun x => (Φ (x/T) : ℂ)) := by
    have := hΦ.1.continuous
    fun_prop
  have hd : Continuous (fun x => ((deriv Φ (x/T)/T : ℝ) : ℂ)) := by
    have h := hΦ.1.continuous_deriv (by simp)
    fun_prop
  have hvc : Continuous (fun x => sharpPrimitive H x-(x : ℂ)*M) := by
    have := sharpPrimitive_continuous H hH
    fun_prop
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hc.continuousOn hvc.continuousOn (fun x _ => hw x) (fun x _ => hv x)
    (hd.intervalIntegrable _ _) ((hH.sub continuous_const).intervalIntegrable _ _)]
  have hφend : Φ (2*T/T)=0 := by
    rw [mul_div_cancel_right₀ (2 : ℝ) hT0.ne']
    exact smoothDyadicWeight_zero_two Φ hΦ
  have hφstart : Φ (1/T)=0 :=
    smoothDyadicWeight_zero_below Φ hΦ ((div_lt_one hT0).mpr hT)
  have hφstart' : Φ T⁻¹=0 := by simpa only [one_div] using hφstart
  simp [hφend, hφstart']

theorem dyadic_smoothing_error_bound {T B E : ℝ} (hT : 1 < T)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (H : ℝ → ℂ) (hH : Continuous H) (M : ℂ)
    (hsharp : ∀ x ∈ Icc T (2*T), ‖sharpPrimitive H x-(x : ℂ)*M‖ ≤ E)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (hderiv : ∀ x : ℝ, |deriv Φ x| ≤ B) :
    ‖∫ t : ℝ, (Φ (t/T) : ℂ)*(H t-M)‖ ≤ 2*B*E := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  rw [dyadic_centered_partial_summation hT H hH M Φ hΦ, norm_neg]
  have hbound (x : ℝ) (hx : x ∈ Set.uIoc 1 (2*T)) :
      ‖((deriv Φ (x/T)/T : ℝ) : ℂ)*(sharpPrimitive H x-(x : ℂ)*M)‖ ≤ B*E/T := by
    rw [Set.uIoc_of_le (by linarith : (1 : ℝ) ≤ 2*T)] at hx
    by_cases hlow : x < T
    · have hz : deriv Φ (x/T)=0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hm
        have h := (hΦ.2 (tsupport_deriv_subset hm)).1
        have h' := (le_div_iff₀ hT0).mp h
        linarith
      simp only [hz, zero_div, Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hT0]
      have hxs : x ∈ Icc T (2*T) := ⟨le_of_not_gt hlow, hx.2⟩
      calc
        _ ≤ (B/T)*E := mul_le_mul
          (div_le_div_of_nonneg_right (hderiv (x/T)) hT0.le) (hsharp x hxs)
          (norm_nonneg _) (by positivity)
        _ = B*E/T := by ring
  calc
    _ ≤ (B*E/T)*|2*T-1| := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ ≤ 2*B*E := by
      rw [abs_of_nonneg (by linarith : 0 ≤ 2*T-1)]
      calc
        _ ≤ (B*E/T)*(2*T) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 2*B*E := by field_simp

theorem dyadic_weighted_integrable {T : ℝ} (hT : 0 < T)
    (H : ℝ → ℂ) (hH : Continuous H) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t => (Φ (t/T) : ℂ)*H t) := by
  have hc : Continuous (fun t => (Φ (t/T) : ℂ)*H t) := by
    have := hΦ.1.continuous
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc T (2*T)))
  intro t ht
  have hn : Φ (t/T) ≠ 0 := by
    intro hz
    simp [Function.mem_support,hz] at ht
  have h := hΦ.2 (subset_tsupport Φ (Function.mem_support.mpr hn))
  exact ⟨by have hh := (le_div_iff₀ hT).mp h.1; linarith,
    (div_le_iff₀ hT).mp h.2⟩

theorem dyadic_weighted_centered_integral {T : ℝ} (hT : 0 < T)
    (H : ℝ → ℂ) (hH : Continuous H) (M : ℂ) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    (∫ t : ℝ, (Φ (t/T) : ℂ)*(H t-M)) =
      (∫ t : ℝ, (Φ (t/T) : ℂ)*H t)-(T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*M := by
  have hiH := dyadic_weighted_integrable hT H hH Φ hΦ
  have hiM := dyadic_weighted_integrable hT (fun _ => M) continuous_const Φ hΦ
  have he : (fun t : ℝ => (Φ (t/T) : ℂ)*(H t-M)) =
      (fun t : ℝ => (Φ (t/T) : ℂ)*H t-(Φ (t/T) : ℂ)*M) := by
    funext t
    ring
  rw [he, integral_sub hiH hiM, integral_mul_const,
    Measure.integral_comp_div (fun x : ℝ => (Φ x : ℂ)) T, abs_of_pos hT,
    Complex.real_smul]

end
end Sechstmoment
