import Sechstmoment.Certificate.Profiles.BetaSupport
import Sechstmoment.Numerator.V.DP.VPolynomialAsymptotic

namespace Sechstmoment
open Complex MeasureTheory Set Metric Filter Polynomial
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 1600000

def betaProfilePolynomial (η : ℝ) (n k : ℕ) : ℝ[X] :=
  Polynomial.C (η⁻¹*(n+1:ℝ)*(Nat.choose n k:ℝ))*
    (1-Polynomial.X)^k*Polynomial.X^(n-k)

theorem betaScaledProfile_eq_polynomial_eval (η : ℝ) (n k : ℕ) (x : ℝ) :
    betaScaledProfile η n k x=(betaProfilePolynomial η n k).eval (1-x/η) := by
  simp only [betaProfilePolynomial,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,
    sub_sub_cancel,betaScaledProfile,betaUnitProfile]
  ring

theorem betaIccProfile_eq_zeroExtendedPolynomialProfile {η : ℝ} (hη : η≠0)
    {n k : ℕ} (hk : k<n) :
    (Icc (0:ℝ) η).indicator (betaScaledProfile η n k)=
      zeroExtendedPolynomialProfile η (betaProfilePolynomial η n k) := by
  funext x
  unfold zeroExtendedPolynomialProfile
  by_cases hx : x∈Ico (0:ℝ) η
  · rw [Set.indicator_of_mem hx,Set.indicator_of_mem (show x∈Icc (0:ℝ) η from ⟨hx.1,hx.2.le⟩)]
    exact betaScaledProfile_eq_polynomial_eval η n k x
  · rw [Set.indicator_of_notMem hx]
    by_cases hx' : x∈Icc (0:ℝ) η
    · rw [Set.indicator_of_mem hx']
      have he : x=η := le_antisymm hx'.2 (by
        by_contra hlt
        exact hx ⟨hx'.1,lt_of_not_ge hlt⟩)
      rw [he]
      exact betaScaled_zero_right hη hk
    · exact Set.indicator_of_notMem hx' _

theorem betaProfileIndex_lt_stage {η a : ℝ} (hη : 0<η) (ha : 0≤a)
    (haη : a<η) {n : ℕ} (hn : 0<n) : betaProfileIndex η a n<n :=
  betaProfileIndex_lt hη ha haη hn

theorem betaProfileIndex_lt_eventually {η a : ℝ} (hη : 0<η)
    (ha : 0<a) (haη : a<η) : ∀ᶠ n : ℕ in atTop, betaProfileIndex η a n<n := by
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact betaProfileIndex_lt hη ha.le haη hn

theorem vEndpointProfile_eq_polynomialProfile {η a : ℝ} (hη : 0<η)
    (ha : 0≤a) (haη : a<η) {n : ℕ} (hn : 0<n) :
    vEndpointProfile η a n=zeroExtendedPolynomialProfile η
      (betaProfilePolynomial η n (betaProfileIndex η a n)) := by
  exact betaIccProfile_eq_zeroExtendedPolynomialProfile hη.ne'
    (betaProfileIndex_lt hη ha haη hn)

theorem vEndpointProfile_eq_polynomialProfile_eventually {η a : ℝ}
    (hη : 0<η) (ha : 0<a) (haη : a<η) :
    ∀ᶠ n : ℕ in atTop, vEndpointProfile η a n=zeroExtendedPolynomialProfile η
      (betaProfilePolynomial η n (betaProfileIndex η a n)) := by
  filter_upwards [betaProfileIndex_lt_eventually hη ha haη] with n hn
  exact betaIccProfile_eq_zeroExtendedPolynomialProfile hη.ne' hn

namespace Source

theorem vBetaRawMixedMoment_tendsto (N : ℕ) (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (a b : ℝ)
    (ha : 0≤a) (haη : a<η) (hb : 0≤b) (hbη : b<η)
    (n m : ℕ) (hn : 0<n) (hm : 0<m) (p : ℝ[X]) (hp : p.natDegree≤N)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => vPolynomialRawMixedMoment T p
      (vEndpointProfile η a n) (vEndpointProfile η b m) Φ/
        ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        finiteDifferentialOperator N (fun j => (p.coeff j.val:ℂ))
          (vReflectedPolynomialJ η
            (betaProfilePolynomial η n (betaProfileIndex η a n))
            (betaProfilePolynomial η m (betaProfileIndex η b m))) 0)) := by
  rw [vEndpointProfile_eq_polynomialProfile hη ha haη hn,
    vEndpointProfile_eq_polynomialProfile hη hb hbη hm]
  exact vPolynomialRawMixedMoment_tendsto N hsource η hη hηu _ _ p hp Φ hΦ

theorem vBetaProjectedMixedMoment_tendsto (N : ℕ) (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (a b : ℝ)
    (ha : 0≤a) (haη : a<η) (hb : 0≤b) (hbη : b<η)
    (n m : ℕ) (hn : 0<n) (hm : 0<m) (p : ℝ[X]) (hp : p.natDegree≤N)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => vPolynomialProjectedMixedMoment T p
      (vEndpointProfile η a n) (vEndpointProfile η b m) Φ/
        ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 (Complex.ofReal (((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        finiteDifferentialOperator N (fun j => (p.coeff j.val:ℂ))
          (vReflectedPolynomialJ η
            (betaProfilePolynomial η n (betaProfileIndex η a n))
            (betaProfilePolynomial η m (betaProfileIndex η b m))) 0).re))) := by
  rw [vEndpointProfile_eq_polynomialProfile hη ha haη hn,
    vEndpointProfile_eq_polynomialProfile hη hb hbη hm]
  exact vPolynomialProjectedMixedMoment_tendsto N hsource η hη hηu _ _ p hp Φ hΦ

theorem vBetaRawMixedMoment_tendsto_eventually (N : ℕ) (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (a b : ℝ)
    (ha : 0<a) (haη : a<η) (hb : 0<b) (hbη : b<η)
    (p : ℝ[X]) (hp : p.natDegree≤N) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ n : ℕ in atTop, Tendsto (fun T : ℝ => vPolynomialRawMixedMoment T p
      (vEndpointProfile η a n) (vEndpointProfile η b n) Φ/
        ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        finiteDifferentialOperator N (fun j => (p.coeff j.val:ℂ))
          (vReflectedPolynomialJ η
            (betaProfilePolynomial η n (betaProfileIndex η a n))
            (betaProfilePolynomial η n (betaProfileIndex η b n))) 0)) := by
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact vBetaRawMixedMoment_tendsto N hsource η hη hηu a b ha.le haη hb.le hbη
    n n hn hn p hp Φ hΦ

theorem vBetaProjectedMixedMoment_tendsto_eventually (N : ℕ) (hsource : DPv2SharpInput)
    (η : ℝ) (hη : 0<η) (hηu : η<1/4) (a b : ℝ)
    (ha : 0<a) (haη : a<η) (hb : 0<b) (hbη : b<η)
    (p : ℝ[X]) (hp : p.natDegree≤N) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ᶠ n : ℕ in atTop, Tendsto (fun T : ℝ => vPolynomialProjectedMixedMoment T p
      (vEndpointProfile η a n) (vEndpointProfile η b n) Φ/
        ((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 (Complex.ofReal (((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
        finiteDifferentialOperator N (fun j => (p.coeff j.val:ℂ))
          (vReflectedPolynomialJ η
            (betaProfilePolynomial η n (betaProfileIndex η a n))
            (betaProfilePolynomial η n (betaProfileIndex η b n))) 0).re))) := by
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact vBetaProjectedMixedMoment_tendsto N hsource η hη hηu a b ha.le haη hb.le hbη
    n n hn hn p hp Φ hΦ

end Source
end
end Sechstmoment
