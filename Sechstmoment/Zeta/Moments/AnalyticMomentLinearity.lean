import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Sechstmoment.Analysis.Profiles.Classes
import Sechstmoment.Zeta.Moments.Definitions

/-!
# Actual source-moment linearity and integrability

The Dirichlet polynomials are finite for the supported profiles. Their
continuity and the compact dyadic weight give actual Lebesgue integrability;
the moment polarization below consequently does not assume integrability as
an additional analytic black box.
-/

namespace Sechstmoment
open Complex MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

theorem profileDirichletSum_add {T : ℝ} (hT : 1 < T) (a : ℝ)
    (f g : ℝ → ℝ) (hf : ∀ x, a < x → f x=0) (hg : ∀ x, a < x → g x=0)
    (s : ℂ) :
    profileDirichletSum T (f+g) s = profileDirichletSum T f s+profileDirichletSum T g s := by
  rw [profileDirichletSum_eq_finite hT a (f+g) (by intro x hx; simp [hf x hx, hg x hx]),
    profileDirichletSum_eq_finite hT a f hf, profileDirichletSum_eq_finite hT a g hg]
  simp [add_div, Finset.sum_add_distrib]

theorem profileDirichletSum_sub {T : ℝ} (hT : 1 < T) (a : ℝ)
    (f g : ℝ → ℝ) (hf : ∀ x, a < x → f x=0) (hg : ∀ x, a < x → g x=0)
    (s : ℂ) :
    profileDirichletSum T (f-g) s = profileDirichletSum T f s-profileDirichletSum T g s := by
  rw [profileDirichletSum_eq_finite hT a (f-g) (by intro x hx; simp [hf x hx, hg x hx]),
    profileDirichletSum_eq_finite hT a f hf, profileDirichletSum_eq_finite hT a g hg]
  simp [sub_div, Finset.sum_sub_distrib]

theorem profileDirichletSum_continuous {T : ℝ} (hT : 1 < T) (a : ℝ)
    (f : ℝ → ℝ) (hf : ∀ x, a < x → f x=0) :
    Continuous (profileDirichletSum T f) := by
  have he : profileDirichletSum T f = fun s =>
      ∑ n ∈ Finset.range ⌊T^a⌋₊,
        (f (Real.log (n+1 : ℝ)/Real.log T) : ℂ)/(n+1 : ℂ)^s := by
    funext s
    exact profileDirichletSum_eq_finite hT a f hf s
  rw [he]
  apply continuous_finsetSum
  intro n _
  have hn : (n+1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n+1 ≠ 0)
  exact continuous_const.div (continuous_id.const_cpow (Or.inl hn))
    (fun s => natCast_add_one_cpow_ne_zero n s)

theorem criticalChi_continuous : Continuous criticalChi := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hs := zetaChi_analyticOnNhd_strip (criticalLinePoint t)
    (by norm_num [criticalLinePoint_re])
  exact hs.continuousAt.comp (by unfold criticalLinePoint; fun_prop)

theorem shiftedFourthProduct_continuous (α : MomentShifts)
    (hα : ∀ j, |(α j).re| < 1/2) : Continuous (fun t => shiftedFourthProduct t α) := by
  have hp (j : Fin 4) : Continuous (fun t => riemannZeta (criticalLinePoint t+α j)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hn : criticalLinePoint t+α j ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [add_re, criticalLinePoint_re, one_re] at hr
      linarith [(abs_lt.mp (hα j)).2]
    exact (analyticOn_riemannZeta _ (by simpa using hn)).continuousAt.comp
      (by unfold criticalLinePoint; fun_prop)
  have hm (j : Fin 4) : Continuous (fun t => riemannZeta (1-criticalLinePoint t+α j)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hn : 1-criticalLinePoint t+α j ≠ 1 := by
      intro he
      have hr := congrArg Complex.re he
      simp only [add_re, sub_re, criticalLinePoint_re, one_re] at hr
      linarith [(abs_lt.mp (hα j)).2]
    exact (analyticOn_riemannZeta _ (by simpa using hn)).continuousAt.comp
      (by unfold criticalLinePoint; fun_prop)
  exact (((hp 0).mul (hp 1)).mul (hm 2)).mul (hm 3)

theorem chiTwistedFourthIntegrand_continuous {T : ℝ} (hT : 1 < T)
    (a : ℝ) (α : MomentShifts) (f g Φ : ℝ → ℝ)
    (hα : ∀ j, |(α j).re| < 1/2)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, a < x → g x=0)
    (hΦ : Continuous Φ) : Continuous (fun t => chiTwistedFourthIntegrand T t α f g Φ) := by
  have hp := shiftedFourthProduct_continuous α hα
  have hf' := profileDirichletSum_continuous hT a f hf
  have hg' := profileDirichletSum_continuous hT a g hg
  have hw : Continuous (fun t => (Φ (t/T) : ℂ)) := by fun_prop
  have hs : Continuous (fun t => 1-criticalLinePoint t) := by
    unfold criticalLinePoint
    fun_prop
  exact ((((hw.mul hp).mul criticalChi_continuous).mul (hf'.comp hs)).mul (hg'.comp hs))

theorem chiTwistedFourthIntegrand_hasCompactSupport {T : ℝ} (hT : 0 < T)
    (α : MomentShifts) (f g Φ : ℝ → ℝ) (hΦ : tsupport Φ ⊆ Icc 1 2) :
    HasCompactSupport (fun t => chiTwistedFourthIntegrand T t α f g Φ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc T (2*T)))
  intro t ht
  by_contra hout
  have hx : t/T ∉ Icc (1 : ℝ) 2 := by
    intro hx
    apply hout
    constructor
    · have h := (le_div_iff₀ hT).mp hx.1
      linarith
    · have h := (div_le_iff₀ hT).mp hx.2
      linarith
  have hzero : Φ (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hΦ h))
  simp [Function.mem_support, chiTwistedFourthIntegrand, hzero] at ht

theorem chiTwistedFourthIntegrand_integrable {T : ℝ} (hT : 1 < T)
    (a : ℝ) (α : MomentShifts) (f g Φ : ℝ → ℝ)
    (hα : ∀ j, |(α j).re| < 1/2)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, a < x → g x=0)
    (hΦ : SmoothDyadicWeight Φ) : Integrable (fun t => chiTwistedFourthIntegrand T t α f g Φ) :=
  (chiTwistedFourthIntegrand_continuous hT a α f g Φ hα hf hg hΦ.1.continuous).integrable_of_hasCompactSupport
      (chiTwistedFourthIntegrand_hasCompactSupport (zero_lt_one.trans hT) α f g Φ hΦ.2)

theorem chiTwistedFourthIntegrand_polarization {T : ℝ} (hT : 1 < T)
    (a t : ℝ) (α : MomentShifts) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, a < x → g x=0) :
    chiTwistedFourthIntegrand T t α f g Φ =
      (1/4 : ℂ)*(chiTwistedFourthIntegrand T t α (f+g) (f+g) Φ-
        chiTwistedFourthIntegrand T t α (f-g) (f-g) Φ) := by
  simp only [chiTwistedFourthIntegrand,
    profileDirichletSum_add hT a f g hf hg, profileDirichletSum_sub hT a f g hf hg]
  ring

theorem chiTwistedFourthMoment_polarization {T : ℝ} (hT : 1 < T)
    (a : ℝ) (α : MomentShifts) (f g Φ : ℝ → ℝ)
    (hα : ∀ j, |(α j).re| < 1/2)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, a < x → g x=0)
    (hΦ : SmoothDyadicWeight Φ) :
    chiTwistedFourthMoment T α f g Φ =
      (1/4 : ℂ)*(chiTwistedFourthMoment T α (f+g) (f+g) Φ-
        chiTwistedFourthMoment T α (f-g) (f-g) Φ) := by
  have hadd : ∀ x, a < x → (f+g) x=0 := by intro x hx; simp [hf x hx, hg x hx]
  have hsub : ∀ x, a < x → (f-g) x=0 := by intro x hx; simp [hf x hx, hg x hx]
  have hiadd := chiTwistedFourthIntegrand_integrable hT a α (f+g) (f+g) Φ hα hadd hadd hΦ
  have hisub := chiTwistedFourthIntegrand_integrable hT a α (f-g) (f-g) Φ hα hsub hsub hΦ
  unfold chiTwistedFourthMoment
  rw [← integral_sub hiadd hisub, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => chiTwistedFourthIntegrand_polarization hT a t α f g Φ hf hg)

end
end Sechstmoment
