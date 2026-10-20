import Sechstmoment.Denominator.Balanced.Asymptotic
import Sechstmoment.Denominator.Gram.Bounds

namespace Sechstmoment
open Complex MeasureTheory Filter Set Polynomial
open scoped Topology BigOperators ComplexConjugate
noncomputable section
set_option maxHeartbeats 0

theorem d06PolynomialAmplitude_self_moment (negative : Bool) (τ : TestType) (T : ℝ)
    (p : ℝ[X]) (f g Φ : ℝ → ℝ) :
    ((∫ t : ℝ,Φ (t/T)*‖d06PolynomialAmplitude negative τ T t p f g‖^2 : ℝ):ℂ) =
      d02BalancedPolynomialMoment T p p (d06SelfProfiles f g) Φ := by
  refine (integral_ofReal (𝕜 := ℂ) (μ := volume)
    (f := fun t : ℝ => Φ (t/T)*‖d06PolynomialAmplitude negative τ T t p f g‖^2)).symm.trans ?_
  unfold d02BalancedPolynomialMoment
  apply integral_congr_ae
  filter_upwards [] with t
  rw [d06PolynomialAmplitude_norm]
  simp only [mul_pow,RCLike.ofReal_mul,RCLike.ofReal_pow,← RCLike.mul_conj]
  rw [← d04_zetaCp_conj]
  have hf : conj (profileDirichletSum T f (criticalLinePoint t)) =
      profileDirichletSum T f (1-criticalLinePoint t) := by
    rw [criticalLinePoint_one_sub]
    exact (profileDirichletSum_conj T f (criticalLinePoint t)).symm
  have hg : conj (profileDirichletSum T g (criticalLinePoint t)) =
      profileDirichletSum T g (1-criticalLinePoint t) := by
    rw [criticalLinePoint_one_sub]
    exact (profileDirichletSum_conj T g (criticalLinePoint t)).symm
  unfold d02BalancedAmplifier d06SelfProfiles
  simp only [hf,hg,Complex.star_def]
  simp
  ring

theorem d06PolynomialAmplitude_self_eventually_bound
    (a b : ℝ) (ha : 0<a) (hb : 0<b) (hab : a+b<1/2)
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfs : tsupport f⊆Icc 0 a) (hgs : tsupport g⊆Icc 0 b)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ)
    (p : ℝ[X]) (hp : p.natDegree≤4) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ T : ℝ in atTop,∀ negative τ,
      (∫ t : ℝ,Φ (t/T)*‖d06PolynomialAmplitude negative τ T t p f g‖^2)/
        (T*(Real.log T)^9)≤B := by
  have hcap : ∀ i,0<d06SelfCaps a b i := by
    intro i
    fin_cases i <;> simp [d06SelfCaps] <;> assumption
  have hsum : (∑ i,d06SelfCaps a b i)<1 := by
    simp [d06SelfCaps,Fin.sum_univ_four]
    linarith
  have hcont : ∀ i,Continuous (d06SelfProfiles f g i) := by
    intro i
    fin_cases i <;> simp [d06SelfProfiles] <;> assumption
  have hsupp : ∀ i,tsupport (d06SelfProfiles f g i)⊆Icc 0 (d06SelfCaps a b i) := by
    intro i
    fin_cases i <;> simp [d06SelfProfiles,d06SelfCaps] <;> assumption
  have ht := d02BalancedDenominatorAsymptotic_closed (d06SelfCaps a b) hcap hsum
    (d06SelfProfiles f g) hcont hsupp Φ hΦ.1 hΦ.2 p p hp hp
  have hbnd := ht.norm.eventually (eventually_lt_nhds (show
      ‖((arithmeticFactor*(∫ x : ℝ,Φ x)*d02BalancedProfileKernel
        (fun i => p.coeff i.val) (fun i => p.coeff i.val) (d06SelfProfiles f g):ℝ):ℂ)‖ <
      ‖((arithmeticFactor*(∫ x : ℝ,Φ x)*d02BalancedProfileKernel
        (fun i => p.coeff i.val) (fun i => p.coeff i.val) (d06SelfProfiles f g):ℝ):ℂ)‖+1 by linarith))
  let B : ℝ := ‖((arithmeticFactor*(∫ x : ℝ,Φ x)*d02BalancedProfileKernel
    (fun i => p.coeff i.val) (fun i => p.coeff i.val) (d06SelfProfiles f g):ℝ):ℂ)‖+1
  refine ⟨B,by dsimp [B]; positivity,?_⟩
  filter_upwards [hbnd,eventually_gt_atTop (1:ℝ)] with T hbound hT
  intro negative τ
  have he := d06PolynomialAmplitude_self_moment negative τ T p f g Φ
  have hnorm : ‖d02BalancedPolynomialMoment T p p (d06SelfProfiles f g) Φ/
      (T*(Real.log T)^9:ℂ)‖ =
      |(∫ t : ℝ,Φ (t/T)*‖d06PolynomialAmplitude negative τ T t p f g‖^2)/
        (T*(Real.log T)^9)| := by
    rw [← he,← Complex.ofReal_pow,← Complex.ofReal_mul,← Complex.ofReal_div,Complex.norm_real,Real.norm_eq_abs]
  rw [hnorm] at hbound
  exact (le_abs_self _).trans hbound.le

end
end Sechstmoment
