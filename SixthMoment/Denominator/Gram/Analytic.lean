import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import SixthMoment.Analysis.Integration.CauchySchwarz
import SixthMoment.Denominator.Unbalanced.Conjugation

namespace SixthMoment
open Complex MeasureTheory Set Polynomial
open scoped Topology ComplexConjugate
noncomputable section

theorem d06_riemannZeta_iteratedDeriv_analyticAt (n : ℕ) (s : ℂ) (hs : s≠1) :
    AnalyticAt ℂ (iteratedDeriv n riemannZeta) s := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using
      (analyticOn_riemannZeta s (by simpa using hs))
  | succ n hn => simpa only [iteratedDeriv_succ] using hn.deriv

theorem d06_centeredZetaDerivative_analyticAt (T : ℝ) (n : ℕ) (s : ℂ) (hs : s≠1) :
    AnalyticAt ℂ (centeredZetaDerivative T n) s := by
  unfold centeredZetaDerivative
  apply Finset.analyticAt_fun_sum
  intro j _
  exact analyticAt_const.mul (d06_riemannZeta_iteratedDeriv_analyticAt j s hs)

theorem d06_centeredZetaDerivative_criticalLine_continuous (T : ℝ) (m : ℕ) :
    Continuous (fun t : ℝ => centeredZetaDerivative T m (criticalLinePoint t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (d06_centeredZetaDerivative_analyticAt T m _ (criticalLinePoint_ne_one t)).continuousAt.comp
    (by unfold criticalLinePoint; fun_prop)

theorem d06_zetaCp_continuous (T : ℝ) (p : ℝ[X]) :
    Continuous (fun t : ℝ => zetaCp T t p) := by
  unfold zetaCp zetaPolynomialDerivative Polynomial.sum
  apply continuous_finsetSum
  intro m _
  exact continuous_const.mul (d06_centeredZetaDerivative_criticalLine_continuous T m)

theorem d06_integral_cauchy_schwarz_of_memLp (F G : ℝ → ℂ)
    (hF : MemLp F 2) (hG : MemLp G 2) :
    ‖∫ t : ℝ, star (G t)*F t‖^2 ≤
      (∫ t : ℝ, ‖F t‖^2)*(∫ t : ℝ, ‖G t‖^2) := by
  have h := integral_cauchy_schwarz (hG.toLp G) (hF.toLp F)
  have hm : (∫ t : ℝ, star ((hG.toLp G) t)*(hF.toLp F) t) =
      ∫ t : ℝ, star (G t)*F t := by
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp,hF.coeFn_toLp] with t htG htF
    rw [htG,htF]
  have hnF : (∫ t : ℝ, ‖(hF.toLp F) t‖^2) = ∫ t : ℝ, ‖F t‖^2 := by
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with t ht
    rw [ht]
  have hnG : (∫ t : ℝ, ‖(hG.toLp G) t‖^2) = ∫ t : ℝ, ‖G t‖^2 := by
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with t ht
    rw [ht]
  rw [hm,hnG,hnF] at h
  simpa only [mul_comm] using h

def d06_dyadicWeightedL2Amplitude (T : ℝ) (Φ : ℝ → ℝ) (F : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.sqrt (Φ (t/T)):ℂ)*F t

theorem d06_dyadicWeightedL2Amplitude_continuous (T : ℝ) (Φ : ℝ → ℝ) (F : ℝ → ℂ)
    (hΦ : Continuous Φ) (hF : Continuous F) :
    Continuous (d06_dyadicWeightedL2Amplitude T Φ F) := by
  unfold d06_dyadicWeightedL2Amplitude
  fun_prop

theorem d06_dyadicWeightedL2Amplitude_hasCompactSupport {T : ℝ} (hT : 0<T)
    (Φ : ℝ → ℝ) (F : ℝ → ℂ) (hΦ : tsupport Φ ⊆ Icc 1 2) :
    HasCompactSupport (d06_dyadicWeightedL2Amplitude T Φ F) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc T (2*T)))
  intro t ht
  by_contra hout
  have hx : t/T ∉ Icc (1:ℝ) 2 := by
    intro hx
    apply hout
    constructor
    · have h := (le_div_iff₀ hT).mp hx.1
      linarith
    · have h := (div_le_iff₀ hT).mp hx.2
      linarith
  have hz : Φ (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hΦ h))
  simp [Function.mem_support,d06_dyadicWeightedL2Amplitude,hz] at ht

theorem d06_dyadicWeightedL2Amplitude_memLp {T : ℝ} (hT : 0<T)
    (Φ : ℝ → ℝ) (F : ℝ → ℂ) (hΦ : SmoothDyadicWeight Φ) (hF : Continuous F) :
    MemLp (d06_dyadicWeightedL2Amplitude T Φ F) 2 :=
  (d06_dyadicWeightedL2Amplitude_continuous T Φ F hΦ.1.continuous hF).memLp_of_hasCompactSupport
    (d06_dyadicWeightedL2Amplitude_hasCompactSupport hT Φ F hΦ.2)

theorem d06_dyadicWeightedL2Amplitude_norm_sq (T : ℝ) (Φ : ℝ → ℝ) (F : ℝ → ℂ)
    (hΦ : ∀ x, 0≤Φ x) (t : ℝ) :
    ‖d06_dyadicWeightedL2Amplitude T Φ F t‖^2 = Φ (t/T)*‖F t‖^2 := by
  simp [d06_dyadicWeightedL2Amplitude,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt (hΦ _)]

theorem d06_weighted_norm_sq_integrable {T : ℝ} (hT : 0<T)
    (Φ : ℝ → ℝ) (F : ℝ → ℂ) (hΦ : SmoothDyadicWeight Φ)
    (hΦpos : ∀ x, 0≤Φ x) (hF : Continuous F) :
    Integrable (fun t : ℝ => Φ (t/T)*‖F t‖^2) := by
  have hm := d06_dyadicWeightedL2Amplitude_memLp hT Φ F hΦ hF
  have hi := (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  simpa only [d06_dyadicWeightedL2Amplitude_norm_sq T Φ F hΦpos] using hi

theorem d06_dyadic_weighted_cauchy_schwarz {T : ℝ} (hT : 0<T)
    (Φ : ℝ → ℝ) (F G : ℝ → ℂ) (hΦ : SmoothDyadicWeight Φ)
    (hΦpos : ∀ x, 0≤Φ x) (hF : Continuous F) (hG : Continuous G) :
    ‖∫ t : ℝ, (Φ (t/T):ℂ)*F t*star (G t)‖^2 ≤
      (∫ t : ℝ, Φ (t/T)*‖F t‖^2)*(∫ t : ℝ, Φ (t/T)*‖G t‖^2) := by
  have h := d06_integral_cauchy_schwarz_of_memLp
    (d06_dyadicWeightedL2Amplitude T Φ F) (d06_dyadicWeightedL2Amplitude T Φ G)
    (d06_dyadicWeightedL2Amplitude_memLp hT Φ F hΦ hF)
    (d06_dyadicWeightedL2Amplitude_memLp hT Φ G hΦ hG)
  have he (t : ℝ) : star (d06_dyadicWeightedL2Amplitude T Φ G t)*
      d06_dyadicWeightedL2Amplitude T Φ F t = (Φ (t/T):ℂ)*F t*star (G t) := by
    simp only [d06_dyadicWeightedL2Amplitude,star_mul,Complex.star_def,conj_ofReal]
    calc
      _ = ((Real.sqrt (Φ (t/T)):ℂ)^2)*F t*conj (G t) := by ring
      _ = _ := by rw [← Complex.ofReal_pow,Real.sq_sqrt (hΦpos _)]
  simp_rw [he,d06_dyadicWeightedL2Amplitude_norm_sq T Φ F hΦpos,
    d06_dyadicWeightedL2Amplitude_norm_sq T Φ G hΦpos] at h
  exact h

theorem d06_weighted_integrable {T : ℝ} (hT : 0<T) (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) (F : ℝ → ℂ) (hF : Continuous F) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*F t) := by
  have hc : Continuous (fun t : ℝ => (Φ (t/T):ℂ)*F t) := by
    exact (Complex.continuous_ofReal.comp (hΦ.1.continuous.comp (by fun_prop))).mul hF
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc : IsCompact (Icc T (2*T)))
  intro t ht
  by_contra hout
  have hx : t/T∉Icc (1:ℝ) 2 := by
    intro hx
    exact hout ⟨by simpa using (le_div_iff₀ hT).mp hx.1,(div_le_iff₀ hT).mp hx.2⟩
  have hz : Φ (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hΦ.2 h))
  simp [Function.mem_support,hz] at ht

end
end SixthMoment
