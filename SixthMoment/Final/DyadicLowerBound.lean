import SixthMoment.Final.CauchySchwarz
import SixthMoment.Zeta.SixthMoment


namespace SixthMoment
open Complex MeasureTheory Set
open scoped Topology BigOperators
noncomputable section

theorem actualSixthMoment_interval_eq_sub (a b : ℝ) :
    (∫ t : ℝ in a..b, ‖riemannZeta (criticalLinePoint t)‖^6) =
      sixthMoment b-sixthMoment a := by
  have hc : Continuous (fun t : ℝ => ‖riemannZeta (criticalLinePoint t)‖^6) :=
    riemannZeta_criticalLine_continuous.norm.pow 6
  have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 a) (hc.intervalIntegrable a b)
  change sixthMoment a+(∫ t : ℝ in a..b, ‖riemannZeta (criticalLinePoint t)‖^6) =
    sixthMoment b at h
  linarith

theorem actualSixthMoment_nonneg {T : ℝ} (hT : 0≤T) : 0≤sixthMoment T :=
  intervalIntegral.integral_nonneg hT (fun _ _ => by positivity)

theorem actualDyadicSixthMoment_le_unweighted {T : ℝ} (hT : 0<T)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦle : ∀ x, Φ x≤1) :
    actualDyadicSixthMoment T Φ ≤
      ∫ t : ℝ in T..2*T, ‖riemannZeta (criticalLinePoint t)‖^6 := by
  have hc : Continuous (fun t : ℝ => ‖riemannZeta (criticalLinePoint t)‖^6) :=
    riemannZeta_criticalLine_continuous.norm.pow 6
  have hw : Continuous (fun t : ℝ => Φ (t/T)*‖riemannZeta (criticalLinePoint t)‖^6) := by
    exact (hΦ.1.continuous.comp (continuous_id.div_const T)).mul hc
  have he : actualDyadicSixthMoment T Φ =
      ∫ t : ℝ in Icc T (2*T), Φ (t/T)*‖riemannZeta (criticalLinePoint t)‖^6 := by
    apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
    intro t ht
    have hx : t/T ∉ Icc (1:ℝ) 2 := by
      intro hx
      apply ht
      constructor
      · have h := (le_div_iff₀ hT).mp hx.1
        linarith
      · have h := (div_le_iff₀ hT).mp hx.2
        linarith
    have hz : Φ (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hΦ.2 h))
    simp only [hz,zero_mul]
  calc
    _ = ∫ t : ℝ in Icc T (2*T), Φ (t/T)*‖riemannZeta (criticalLinePoint t)‖^6 := he
    _ ≤ ∫ t : ℝ in Icc T (2*T), ‖riemannZeta (criticalLinePoint t)‖^6 := by
      apply setIntegral_mono_on hw.integrableOn_Icc hc.integrableOn_Icc measurableSet_Icc
      intro t _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hΦle (t/T)) (by positivity :
        0≤‖riemannZeta (criticalLinePoint t)‖^6)
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le (by linarith)]

theorem actual250ProjectedMixedMoment_unweighted_lower_bound (n : ℕ) (hn : 0<n)
    {T : ℝ} (hT : 1<T) (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (hΦpos : ∀ x, 0≤Φ x) (hΦle : ∀ x, Φ x≤1)
    (hg : 0<actual250ProjectedGramMoment n T Φ) :
    ‖actual250ProjectedMixedMoment n T Φ‖^2/actual250ProjectedGramMoment n T Φ ≤
      ∫ t : ℝ in T..2*T, ‖riemannZeta (criticalLinePoint t)‖^6 :=
  (actual250ProjectedMixedMoment_quotient_lower_bound n hn hT Φ hΦ hΦpos hg).trans
    (actualDyadicSixthMoment_le_unweighted (zero_lt_one.trans hT) Φ hΦ hΦle)

theorem actualSixthMoment_finite_dyadic_sum (T : ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J,
      ∫ t : ℝ in (T/(2:ℝ)^(j+1))..(T/(2:ℝ)^j),
        ‖riemannZeta (criticalLinePoint t)‖^6) =
      sixthMoment T-sixthMoment (T/(2:ℝ)^J) := by
  induction J with
  | zero => simp
  | succ J hJ =>
    rw [Finset.sum_range_succ,hJ,actualSixthMoment_interval_eq_sub]
    ring

theorem actualSixthMoment_finite_dyadic_sum_le {T : ℝ} (hT : 0≤T) (J : ℕ) :
    (∑ j ∈ Finset.range J,
      ∫ t : ℝ in (T/(2:ℝ)^(j+1))..(T/(2:ℝ)^j),
        ‖riemannZeta (criticalLinePoint t)‖^6) ≤ sixthMoment T := by
  rw [actualSixthMoment_finite_dyadic_sum]
  exact sub_le_self _ (actualSixthMoment_nonneg (div_nonneg hT (by positivity)))

theorem actual250ProjectedMixedMoment_finite_dyadic_lower_bound
    (n : ℕ) (hn : 0<n) (J : ℕ) {T : ℝ} (hT : (2:ℝ)^J<T)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) (hΦpos : ∀ x, 0≤Φ x)
    (hΦle : ∀ x, Φ x≤1)
    (hg : ∀ j<J, 0<actual250ProjectedGramMoment n (T/(2:ℝ)^(j+1)) Φ) :
    (∑ j ∈ Finset.range J,
      ‖actual250ProjectedMixedMoment n (T/(2:ℝ)^(j+1)) Φ‖^2/
        actual250ProjectedGramMoment n (T/(2:ℝ)^(j+1)) Φ) ≤ sixthMoment T := by
  apply le_trans (Finset.sum_le_sum ?_)
    (actualSixthMoment_finite_dyadic_sum_le
      (le_of_lt ((by positivity : (0:ℝ)<2^J).trans hT)) J)
  intro j hj
  have hjJ : j<J := Finset.mem_range.mp hj
  have hp : (2:ℝ)^(j+1)≤2^J := pow_le_pow_right₀ (by norm_num) (by omega)
  have hh : 1<T/(2:ℝ)^(j+1) := (lt_div_iff₀ (by positivity)).mpr (by simpa using hp.trans_lt hT)
  have h := actual250ProjectedMixedMoment_unweighted_lower_bound n hn hh Φ hΦ hΦpos hΦle
    (hg j hjJ)
  have he : 2*(T/(2:ℝ)^(j+1))=T/(2:ℝ)^j := by
    rw [pow_succ]
    field_simp
  simpa only [he] using h

end
end SixthMoment
