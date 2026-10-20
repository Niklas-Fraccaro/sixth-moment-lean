import Mathlib.Analysis.Calculus.Deriv.Star
import SixthMoment.Denominator.Unbalanced.ActualCircleFubini

namespace SixthMoment
open MeasureTheory Set Complex Polynomial Filter
open scoped BigOperators Topology ComplexConjugate ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem d04_riemannZeta_iteratedDeriv_conj (n : ℕ) (s : ℂ) :
    iteratedDeriv n riemannZeta (conj s) = conj (iteratedDeriv n riemannZeta s) := by
  induction n generalizing s with
  | zero => simpa only [iteratedDeriv_zero] using riemannZeta_conj s
  | succ n hn =>
    have he : (fun z => conj (iteratedDeriv n riemannZeta (conj z))) =
        iteratedDeriv n riemannZeta := by
      funext z
      rw [hn,conj_conj]
    have he' : (conj ∘ iteratedDeriv n riemannZeta ∘ conj) =
        iteratedDeriv n riemannZeta := he
    have hd := congrFun (deriv_conj_conj (f := iteratedDeriv n riemannZeta)) s
    rw [he'] at hd
    simp only [Function.comp_apply] at hd
    rw [← iteratedDeriv_succ] at hd
    have hh := congrArg conj hd
    simpa only [conj_conj] using hh.symm

theorem d04_centeredZetaDerivative_conj (T : ℝ) (n : ℕ) (s : ℂ) :
    centeredZetaDerivative T n (conj s) = conj (centeredZetaDerivative T n s) := by
  simp only [centeredZetaDerivative,map_sum,map_mul,map_div₀,map_pow,
    conj_natCast,conj_ofReal,map_one,map_ofNat,d04_riemannZeta_iteratedDeriv_conj]

theorem d04_zetaCp_conj (T t : ℝ) (p : ℝ[X]) :
    star (zetaCp T t p) = zetaPolynomialDerivative T p (1-criticalLinePoint t) := by
  rw [criticalLinePoint_one_sub]
  change conj (zetaPolynomialDerivative T p (criticalLinePoint t)) = _
  unfold zetaPolynomialDerivative
  rw [Polynomial.sum_def,Polynomial.sum_def,map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_mul,conj_ofReal,← d04_centeredZetaDerivative_conj]
  rfl

def d04UnbalancedConjugateProfiles (ρ : Fin 4 → ℝ → ℝ) : Fin 4 → ℝ → ℝ :=
  ![ρ 1,ρ 2,ρ 3,ρ 0]

def d04UnbalancedPlusAmplifier (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  profileDirichletSum T (ρ 0) (criticalLinePoint t) *
    profileDirichletSum T (ρ 1) (1-criticalLinePoint t) *
    profileDirichletSum T (ρ 2) (1-criticalLinePoint t) *
    profileDirichletSum T (ρ 3) (1-criticalLinePoint t)

def d04UnbalancedPlusPolynomialMoment (T : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ) * criticalChi t * zetaCp T t p *
    zetaPolynomialDerivative T q (1-criticalLinePoint t) *
      d04UnbalancedPlusAmplifier T t ρ

def d04UnbalancedPlusProfileKernel (p q : Fin 5 → ℝ)
    (ρ : Fin 4 → ℝ → ℝ) : ℝ :=
  d04UnbalancedProfileKernel q p (d04UnbalancedConjugateProfiles ρ)

def d04UnbalancedConjugateCaps (A : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![A 1,A 2,A 3,A 0]

theorem d04UnbalancedConjugateCaps_sum (A : Fin 4 → ℝ) :
    (∑ i, d04UnbalancedConjugateCaps A i) = ∑ i, A i := by
  simp [d04UnbalancedConjugateCaps,Fin.sum_univ_succ]
  ring

theorem d04UnbalancedConjugateCaps_positive (A : Fin 4 → ℝ)
    (hA : ∀ i, 0<A i) : ∀ i, 0<d04UnbalancedConjugateCaps A i := by
  intro i
  fin_cases i <;> simp [d04UnbalancedConjugateCaps] <;> exact hA _

theorem d04UnbalancedConjugateProfiles_continuous (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i, Continuous (ρ i)) :
    ∀ i, Continuous (d04UnbalancedConjugateProfiles ρ i) := by
  intro i
  fin_cases i <;> simp [d04UnbalancedConjugateProfiles] <;> exact hρ _

theorem d04UnbalancedConjugateProfiles_tsupport (ρ : Fin 4 → ℝ → ℝ)
    (A : Fin 4 → ℝ) (hρ : ∀ i, tsupport (ρ i) ⊆ Icc 0 (A i)) :
    ∀ i, tsupport (d04UnbalancedConjugateProfiles ρ i) ⊆
      Icc 0 (d04UnbalancedConjugateCaps A i) := by
  intro i
  fin_cases i <;> simp [d04UnbalancedConjugateProfiles,d04UnbalancedConjugateCaps] <;>
    exact hρ _

theorem d04_criticalChi_conj (t : ℝ) : conj (criticalChi t) = (criticalChi t)⁻¹ := by
  have h := criticalChi_mul_star t
  exact ((mul_eq_one_iff_inv_eq₀ (d04_criticalChi_ne_zero t)).mp h).symm

theorem d04_criticalChi_inv_conj (t : ℝ) : conj ((criticalChi t)⁻¹) = criticalChi t := by
  rw [map_inv₀, d04_criticalChi_conj, inv_inv]

theorem d04UnbalancedAmplifier_conj (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) :
    conj (d04UnbalancedAmplifier T t (d04UnbalancedConjugateProfiles ρ)) =
      d04UnbalancedPlusAmplifier T t ρ := by
  have hplus (f : ℝ → ℝ) : conj (profileDirichletSum T f (criticalLinePoint t)) =
      profileDirichletSum T f (1-criticalLinePoint t) := by
    rw [criticalLinePoint_one_sub]
    exact (profileDirichletSum_conj T f (criticalLinePoint t)).symm
  have hminus (f : ℝ → ℝ) : conj (profileDirichletSum T f (1-criticalLinePoint t)) =
      profileDirichletSum T f (criticalLinePoint t) := by
    rw [criticalLinePoint_one_sub]
    change conj (profileDirichletSum T f (conj (criticalLinePoint t))) = _
    rw [profileDirichletSum_conj,conj_conj]
  change conj (profileDirichletSum T (ρ 1) (criticalLinePoint t) *
    profileDirichletSum T (ρ 2) (criticalLinePoint t) *
    profileDirichletSum T (ρ 3) (criticalLinePoint t) *
    profileDirichletSum T (ρ 0) (1-criticalLinePoint t)) =
      profileDirichletSum T (ρ 0) (criticalLinePoint t) *
      profileDirichletSum T (ρ 1) (1-criticalLinePoint t) *
      profileDirichletSum T (ρ 2) (1-criticalLinePoint t) *
      profileDirichletSum T (ρ 3) (1-criticalLinePoint t)
  simp only [map_mul,hplus,hminus]
  ring

theorem d04UnbalancedPlusPolynomialMoment_eq_conj (T : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) :
    d04UnbalancedPlusPolynomialMoment T p q ρ Φ =
      conj (d04UnbalancedPolynomialMoment T q p (d04UnbalancedConjugateProfiles ρ) Φ) := by
  unfold d04UnbalancedPlusPolynomialMoment d04UnbalancedPolynomialMoment
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  have hlow : conj (zetaPolynomialDerivative T p (1-criticalLinePoint t)) = zetaCp T t p := by
    change star (zetaPolynomialDerivative T p (1-criticalLinePoint t)) = zetaCp T t p
    rw [← d04_zetaCp_conj,star_star]
  simp only [map_mul,conj_ofReal,d04_criticalChi_inv_conj,
    show conj (zetaCp T t q) = zetaPolynomialDerivative T q (1-criticalLinePoint t)
      from d04_zetaCp_conj T t q,hlow,d04UnbalancedAmplifier_conj]
  ring

theorem d04UnbalancedPlusPolynomialMoment_normalized_eq_conj (T : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) :
    d04UnbalancedPlusPolynomialMoment T p q ρ Φ / (T*(Real.log T)^9 : ℂ) =
      conj (d04UnbalancedPolynomialMoment T q p (d04UnbalancedConjugateProfiles ρ) Φ /
        (T*(Real.log T)^9 : ℂ)) := by
  rw [map_div₀,d04UnbalancedPlusPolynomialMoment_eq_conj]
  simp

theorem d04UnbalancedPlusPolynomialMoment_tendsto_of_minus (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) (L : ℝ)
    (h : Tendsto (fun T : ℝ =>
      d04UnbalancedPolynomialMoment T q p (d04UnbalancedConjugateProfiles ρ) Φ /
        (T*(Real.log T)^9 : ℂ)) atTop (𝓝 (L : ℂ))) :
    Tendsto (fun T : ℝ => d04UnbalancedPlusPolynomialMoment T p q ρ Φ /
      (T*(Real.log T)^9 : ℂ)) atTop (𝓝 (L : ℂ)) := by
  simpa only [d04UnbalancedPlusPolynomialMoment_normalized_eq_conj,
    Function.comp_def,conj_ofReal]
    using Complex.continuous_conj.continuousAt.tendsto.comp h

def D04UnbalancedPlusAsymptotic : Prop :=
  ∀ (a : Fin 4 → ℝ), (∀ i, 0 < a i) → (∑ i, a i) < 1 →
  ∀ (ρ : Fin 4 → ℝ → ℝ), (∀ i, Continuous (ρ i)) →
    (∀ i, tsupport (ρ i) ⊆ Icc 0 (a i)) →
  ∀ (Φ : ℝ → ℝ), ContDiff ℝ ∞ Φ → tsupport Φ ⊆ Icc 1 2 →
  ∀ (p q : ℝ[X]), p.natDegree ≤ 4 → q.natDegree ≤ 4 →
    Tendsto (fun T : ℝ => d04UnbalancedPlusPolynomialMoment T p q ρ Φ /
      (T*(Real.log T)^9 : ℂ)) atTop
      (𝓝 ((arithmeticFactor * (∫ x : ℝ, Φ x) *
        d04UnbalancedPlusProfileKernel (fun i => p.coeff i.val)
          (fun i => q.coeff i.val) ρ : ℝ) : ℂ))

theorem d04UnbalancedPlusAsymptotic_of_minus
    (hminus : D04UnbalancedMinusAsymptotic) : D04UnbalancedPlusAsymptotic := by
  intro a ha hsum ρ hρ hρs Φ hΦ hΦs p q hp hq
  apply d04UnbalancedPlusPolynomialMoment_tendsto_of_minus p q ρ Φ
    (arithmeticFactor * (∫ x : ℝ, Φ x) *
      d04UnbalancedPlusProfileKernel (fun i => p.coeff i.val) (fun i => q.coeff i.val) ρ)
  exact hminus (d04UnbalancedConjugateCaps a)
    (d04UnbalancedConjugateCaps_positive a ha)
    (by simpa only [d04UnbalancedConjugateCaps_sum] using hsum)
    (d04UnbalancedConjugateProfiles ρ)
    (d04UnbalancedConjugateProfiles_continuous ρ hρ)
    (d04UnbalancedConjugateProfiles_tsupport ρ a hρs) Φ hΦ hΦs q p hq hp

end
end SixthMoment
