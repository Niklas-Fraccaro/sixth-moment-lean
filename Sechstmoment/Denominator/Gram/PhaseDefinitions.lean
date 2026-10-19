import Sechstmoment.Denominator.Unbalanced.Conjugation
import Sechstmoment.Denominator.Unbalanced.MomentErrorBudget

/-! The two extreme denominator phases, before any vanishing assertion.
The minus phase has four positive Dirichlet factors and the literal
`χ⁻² C⁺ C⁻` pair. The plus phase is its exact complex conjugate. -/
namespace Sechstmoment
open Complex Real Polynomial MeasureTheory Filter Set
open scoped BigOperators Topology ComplexConjugate ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def d06AllPositiveAmplifier (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  ∏ i, profileDirichletSum T (ρ i) (criticalLinePoint t)

def d06AllNegativeAmplifier (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) : ℂ :=
  ∏ i, profileDirichletSum T (ρ i) (1-criticalLinePoint t)

def d06ExtremeMinusShiftedMoment (T : ℝ) (σ : Fin 2 → ℂ)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ)*(criticalChi t)⁻¹*(criticalChi t)⁻¹*
    zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1)*d06AllPositiveAmplifier T t ρ

def d06ExtremeMinusPolynomialMoment (T : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ)*(criticalChi t)⁻¹*(criticalChi t)⁻¹*
    zetaCp T t p*zetaPolynomialDerivative T q (1-criticalLinePoint t)*
      d06AllPositiveAmplifier T t ρ

def d06ExtremePlusPolynomialMoment (T : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ)*criticalChi t*criticalChi t*
    zetaCp T t p*zetaPolynomialDerivative T q (1-criticalLinePoint t)*
      d06AllNegativeAmplifier T t ρ

def d06ExtremeOneSidedMoment (T : ℝ) (σ : Fin 2 → ℂ)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ)*(criticalChi t)⁻¹*
    d04CenteringPurePower T t (σ 0)*d04OneSidedCenteredPair T t σ*
      d06AllPositiveAmplifier T t ρ

def d06ExtremeMomentError (T : ℝ) (σ : Fin 2 → ℂ)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T) : ℂ)*d06AllPositiveAmplifier T t ρ*(criticalChi t)⁻¹*
    ((criticalChi t)⁻¹*zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1)-
      d04CenteringPurePower T t (σ 0)*d04OneSidedCenteredPair T t σ)

theorem d06AllPositiveAmplifier_conj (T t : ℝ) (ρ : Fin 4 → ℝ → ℝ) :
    conj (d06AllPositiveAmplifier T t ρ)=d06AllNegativeAmplifier T t ρ := by
  unfold d06AllPositiveAmplifier d06AllNegativeAmplifier
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [criticalLinePoint_one_sub]
  exact (profileDirichletSum_conj T (ρ i) (criticalLinePoint t)).symm

theorem d06AllPositiveAmplifier_norm_eq_unbalanced (T t : ℝ)
    (ρ : Fin 4 → ℝ → ℝ) :
    ‖d06AllPositiveAmplifier T t ρ‖=‖d04UnbalancedAmplifier T t ρ‖ := by
  have h : ‖profileDirichletSum T (ρ 3) (1-criticalLinePoint t)‖=
      ‖profileDirichletSum T (ρ 3) (criticalLinePoint t)‖ := by
    rw [criticalLinePoint_one_sub]
    change ‖profileDirichletSum T (ρ 3) (conj (criticalLinePoint t))‖= _
    rw [profileDirichletSum_conj]
    exact norm_conj _
  simp only [d06AllPositiveAmplifier,Fin.prod_univ_four,d04UnbalancedAmplifier,norm_mul,h]

theorem d06AllPositiveAmplifier_norm_le {T : ℝ} (hT : 1<T) (t : ℝ)
    (a M : Fin 4 → ℝ) (hM : ∀ i,0≤M i) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i x,|ρ i x|≤M i) (hcap : ∀ i x,a i<x → ρ i x=0) :
    ‖d06AllPositiveAmplifier T t ρ‖≤(∏ i,2*M i)*T^((∑ i,a i)/2) := by
  rw [d06AllPositiveAmplifier_norm_eq_unbalanced]
  exact d04UnbalancedAmplifier_norm_le hT t a M hM ρ hρ hcap

theorem d06AllPositiveAmplifier_continuous {T : ℝ} (hT : 1<T)
    (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (hρs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i)) :
    Continuous (fun t => d06AllPositiveAmplifier T t ρ) := by
  have hp (i : Fin 4) : Continuous (fun t => profileDirichletSum T (ρ i) (criticalLinePoint t)) := by
    have hz : ∀ x : ℝ,a i<x → ρ i x=0 := by
      intro x hx
      by_contra hn
      exact (not_le_of_gt hx) (hρs i (subset_tsupport (ρ i) hn)).2
    have he := profileDirichletSum_eq_finite hT (a i) (ρ i) hz
    simp_rw [he]
    apply continuous_finsetSum
    intro n _
    have hne : (n+1 : ℂ)≠0 := by
      have hh : (0:ℝ)<(n+1 : ℝ) := by positivity
      exact_mod_cast hh.ne'
    simp_rw [Complex.cpow_def_of_ne_zero hne]
    have hden (t : ℝ) : Complex.exp (Complex.log (n+1 : ℂ)*criticalLinePoint t)≠0 :=
      Complex.exp_ne_zero _
    exact continuous_const.div (by unfold criticalLinePoint; fun_prop) hden
  unfold d06AllPositiveAmplifier
  exact continuous_finsetProd _ (fun i _ => hp i)

theorem d06ExtremePlusPolynomialMoment_eq_conj (T : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) :
    d06ExtremePlusPolynomialMoment T p q ρ Φ=
      conj (d06ExtremeMinusPolynomialMoment T q p ρ Φ) := by
  unfold d06ExtremePlusPolynomialMoment d06ExtremeMinusPolynomialMoment
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with t
  have hlow : conj (zetaPolynomialDerivative T p (1-criticalLinePoint t))=zetaCp T t p := by
    change star (zetaPolynomialDerivative T p (1-criticalLinePoint t))=zetaCp T t p
    rw [← d04_zetaCp_conj,star_star]
  simp only [map_mul,conj_ofReal,d04_criticalChi_inv_conj,d06AllPositiveAmplifier_conj,
    show conj (zetaCp T t q)=zetaPolynomialDerivative T q (1-criticalLinePoint t)
      from d04_zetaCp_conj T t q,hlow]
  ring

theorem d06ExtremePlusPolynomialMoment_normalized_eq_conj (T : ℝ) (p q : ℝ[X])
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) :
    d06ExtremePlusPolynomialMoment T p q ρ Φ/(T*(Real.log T)^9 : ℂ)=
      conj (d06ExtremeMinusPolynomialMoment T q p ρ Φ/(T*(Real.log T)^9 : ℂ)) := by
  rw [map_div₀,d06ExtremePlusPolynomialMoment_eq_conj]
  simp

def D06ExtremeMinusVanishing : Prop :=
  ∀ (a : Fin 4 → ℝ), (∀ i,0<a i) → (∑ i,a i)<1 →
  ∀ (ρ : Fin 4 → ℝ → ℝ), (∀ i,Continuous (ρ i)) →
    (∀ i,tsupport (ρ i)⊆Icc 0 (a i)) →
  ∀ (Φ : ℝ → ℝ), ContDiff ℝ ∞ Φ → tsupport Φ⊆Icc 1 2 →
  ∀ (p q : ℝ[X]), p.natDegree≤4 → q.natDegree≤4 →
    Tendsto (fun T : ℝ => d06ExtremeMinusPolynomialMoment T p q ρ Φ/
      (T*(Real.log T)^9 : ℂ)) atTop (𝓝 0)

def D06ExtremePlusVanishing : Prop :=
  ∀ (a : Fin 4 → ℝ), (∀ i,0<a i) → (∑ i,a i)<1 →
  ∀ (ρ : Fin 4 → ℝ → ℝ), (∀ i,Continuous (ρ i)) →
    (∀ i,tsupport (ρ i)⊆Icc 0 (a i)) →
  ∀ (Φ : ℝ → ℝ), ContDiff ℝ ∞ Φ → tsupport Φ⊆Icc 1 2 →
  ∀ (p q : ℝ[X]), p.natDegree≤4 → q.natDegree≤4 →
    Tendsto (fun T : ℝ => d06ExtremePlusPolynomialMoment T p q ρ Φ/
      (T*(Real.log T)^9 : ℂ)) atTop (𝓝 0)

theorem d06ExtremePlusVanishing_of_minus
    (hminus : D06ExtremeMinusVanishing) : D06ExtremePlusVanishing := by
  intro a ha hsum ρ hρ hρs Φ hΦ hΦs p q hp hq
  simpa only [d06ExtremePlusPolynomialMoment_normalized_eq_conj,
    Function.comp_def,map_zero] using
    Complex.continuous_conj.continuousAt.tendsto.comp
      (hminus a ha hsum ρ hρ hρs Φ hΦ hΦs q p hq hp)

end
end Sechstmoment
