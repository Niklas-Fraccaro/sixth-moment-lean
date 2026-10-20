import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
import Sechstmoment.Numerator.U.Reconstruction.RectangularAFEReconstruction


namespace Sechstmoment
open Complex Source MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology

theorem rectangular_supported_profile_bounded {a : ℝ} (f : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hf.2.1.exists_bound_of_continuous hf.1.continuous
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x
  exact (hM x).trans (le_max_left _ _)

theorem rectangular_supported_profile_zero_above {a : ℝ} (f : ℝ → ℝ)
    (hf : SmoothInteriorProfile a f) : ∀ x, a < x → f x = 0 := by
  intro x hx
  by_contra hn
  have hm : x ∈ tsupport f := subset_tsupport f (by simpa only [Function.mem_support] using hn)
  have := (hf.2.2 hm).2
  linarith

theorem rectangular_profileDirichletSum_norm_le {T M : ℝ} (hT : 1 < T) (hM : 0 ≤ M)
    (a : ℝ) (f : ℝ → ℝ) (hf : ∀ x, a < x → f x = 0) (hb : ∀ x, ‖f x‖ ≤ M)
    (s : ℂ) (hs : 0 ≤ s.re) : ‖profileDirichletSum T f s‖ ≤ M*T^a := by
  rw [profileDirichletSum_eq_finite hT a f hf]
  have he : ∀ n : ℕ, ‖(f (Real.log (n+1:ℝ)/Real.log T) : ℂ)/(n+1:ℂ)^s‖ ≤ M := by
    intro n
    have hn : (1:ℝ) ≤ n+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have hpos : (0:ℝ) < n+1 := by positivity
    have hden : 1 ≤ ‖(n+1:ℂ)^s‖ := by
      rw [show (n+1:ℂ) = ((n+1:ℝ):ℂ) by norm_cast,
        Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      exact Real.one_le_rpow hn hs
    rw [norm_div, Complex.norm_real]
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hden)).mpr
    have hfbound := hb (Real.log (n+1:ℝ)/Real.log T)
    rw [Real.norm_eq_abs] at hfbound
    exact hfbound.trans (le_mul_of_one_le_right hM hden)
  calc
    _ ≤ ∑ _n ∈ Finset.range ⌊T^a⌋₊, M :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun n _ => he n))
    _ = (⌊T^a⌋₊:ℝ)*M := by simp
    _ ≤ T^a*M := mul_le_mul_of_nonneg_right (Nat.floor_le (Real.rpow_nonneg (by linarith) _)) hM
    _ = _ := by ring

noncomputable def rectangularAFEErrorIntegrand (T : ℝ) (α : MomentShifts)
    (G : ℂ → ℂ) (f g Φ : ℝ → ℝ) (t : ℝ) : ℂ :=
  (Φ (t/T):ℂ)*profileDirichletSum T f (criticalLinePoint t)*
    profileDirichletSum T g (1-criticalLinePoint t)*bblrAFEDiscrepancy G α t

noncomputable def rectangularAFEIntegratedError (T : ℝ) (α : MomentShifts)
    (G : ℂ → ℂ) (f g Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, rectangularAFEErrorIntegrand T α G f g Φ t

theorem rectangular_AFE_error_zero_outside {T : ℝ} (hT : 0 < T)
    (α : MomentShifts) (G : ℂ → ℂ) (f g Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (t : ℝ) (ht : t ∉ Icc T (2*T)) : rectangularAFEErrorIntegrand T α G f g Φ t = 0 := by
  have hz : Φ (t/T) = 0 := by
    by_contra hn
    have hs : t/T ∈ tsupport Φ := subset_tsupport Φ (by simpa only [Function.mem_support] using hn)
    obtain ⟨hl, hu⟩ := hΦ.2 hs
    apply ht
    exact ⟨by nlinarith [(le_div_iff₀ hT).mp hl], by nlinarith [(div_le_iff₀ hT).mp hu]⟩
  simp [rectangularAFEErrorIntegrand, hz]

theorem rectangular_AFE_integrated_error_bound {T F Gc P C A : ℝ}
    (hT : 1 < T) (hF : 0 ≤ F) (hGc : 0 ≤ Gc) (hP : 0 ≤ P) (_hC : 0 ≤ C)
    (a b : ℝ) (f g Φ : ℝ → ℝ) (α : MomentShifts) (G : ℂ → ℂ)
    (hf : ∀ x, a < x → f x = 0) (hg : ∀ x, b < x → g x = 0)
    (hfb : ∀ x, ‖f x‖ ≤ F) (hgb : ∀ x, ‖g x‖ ≤ Gc)
    (hΦ : SmoothDyadicWeight Φ) (hΦb : ∀ x, ‖Φ x‖ ≤ P)
    (hsource : ∀ t ∈ Icc T (2*T), ‖bblrAFEDiscrepancy G α t‖ ≤ C*T^(-A)) :
    ‖rectangularAFEIntegratedError T α G f g Φ‖ ≤ (P*F*Gc*C)*T^(1+a+b-A) := by
  have ht : 0 < T := lt_trans zero_lt_one hT
  have hb : ∀ t ∈ Icc T (2*T), ‖rectangularAFEErrorIntegrand T α G f g Φ t‖ ≤
      (P*F*Gc*C)*T^(a+b-A) := by
    intro t hmem
    have hfT := rectangular_profileDirichletSum_norm_le hT hF a f hf hfb (criticalLinePoint t)
      (by norm_num [criticalLinePoint])
    have hgT := rectangular_profileDirichletSum_norm_le hT hGc b g hg hgb (1-criticalLinePoint t)
      (by norm_num [criticalLinePoint])
    have hweight : ‖(Φ (t/T):ℂ)‖ ≤ P := by simpa only [Complex.norm_real] using hΦb (t/T)
    dsimp [rectangularAFEErrorIntegrand]
    rw [norm_mul, norm_mul, norm_mul]
    calc
      _ ≤ P*(F*T^a)*(Gc*T^b)*(C*T^(-A)) := by gcongr; exact hsource t hmem
      _ = _ := by
        calc
          _ = (P*F*Gc*C)*(T^a*T^b*T^(-A)) := by ring
          _ = _ := by rw [← Real.rpow_add ht, ← Real.rpow_add ht]; congr 1
  have hset : rectangularAFEIntegratedError T α G f g Φ =
      ∫ t : ℝ in Icc T (2*T), rectangularAFEErrorIntegrand T α G f g Φ t := by
    unfold rectangularAFEIntegratedError
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases htmem : t ∈ Icc T (2*T)
    · simp only [indicator_of_mem htmem]
    · simp only [indicator_of_notMem htmem, rectangular_AFE_error_zero_outside ht α G f g Φ hΦ t htmem]
  rw [hset]
  have hi := norm_setIntegral_le_of_norm_le_const (measure_Icc_lt_top (μ := volume) (a := T) (b := 2*T)) hb
  have hmeasure : volume.real (Icc T (2*T)) = T := by
    rw [Real.volume_real_Icc]
    simp only [show 2*T-T = T by ring, max_eq_left ht.le]
  rw [hmeasure] at hi
  calc
    _ ≤ ((P*F*Gc*C)*T^(a+b-A))*T := hi
    _ = _ := by
      calc
        _ = (P*F*Gc*C)*(T^(a+b-A)*T^(1:ℝ)) := by rw [Real.rpow_one]; ring
        _ = _ := by rw [← Real.rpow_add ht]; congr 1; ring

end Sechstmoment
