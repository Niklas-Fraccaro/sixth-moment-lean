import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Sechstmoment.Denominator.Balanced.MomentErrorBudget
import Sechstmoment.Denominator.Balanced.ZetaGaussianPair

/-! The full proved zeta-pair replacement error after multiplication by
the four actual profiles and integration over the physical height window. -/
namespace Sechstmoment
open Complex Real Source MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
noncomputable section

def d02ZetaGaussianMomentError (T : ℝ) (σ : SecondMomentShifts)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ,(Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*
    (zetaCPlus T t (σ 0)*zetaCMinus T t (σ 1)-d02CenteredGaussianPair T t σ)

theorem d02Continuous_supported_norm_bound {f : ℝ → ℝ} {a b : ℝ}
    (hf : Continuous f) (hs : tsupport f⊆Icc a b) :
    ∃ M : ℝ,0≤M ∧ ∀ x,|f x|≤M := by
  have hc : HasCompactSupport f := isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) hs
  obtain ⟨M,hM⟩ := hc.exists_bound_of_continuous hf
  refine ⟨max 0 M,le_max_left _ _,fun x => ?_⟩
  have hx : |f x|≤M := by simpa only [Real.norm_eq_abs] using hM x
  exact hx.trans (le_max_right _ _)

/-- The actual Gamma and chi errors have a strictly smaller-than-height
power whenever `1/2+2ε+S/2<1`.  No error or negligibility assertion is input. -/
theorem d02ZetaGaussianMomentError_uniform_bound {R ε : ℝ}
    (hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ i,Continuous (ρ i)) (hs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : SecondMomentShifts,
      (∀ j,‖σ j‖≤R) → ‖d02ZetaGaussianMomentError T σ ρ Φ‖≤
        C*T^(1/2+2*ε+(∑ i,a i)/2) := by
  have hM : ∀ i,∃ M : ℝ,0≤M ∧ ∀ x,|ρ i x|≤M :=
    fun i => d02Continuous_supported_norm_bound (hρ i) (hs i)
  choose M hM hρM using hM
  obtain ⟨P,hP,hΦP⟩ := d02Continuous_supported_norm_bound hΦ hΦs
  obtain ⟨K,hK,hpoint⟩ := d02ZetaPair_gaussian_window_error hR hε hε1
  have hprod : 0≤∏ i,2*M i :=
    Finset.prod_nonneg fun i _ => mul_nonneg (by norm_num) (hM i)
  refine ⟨P*(∏ i,2*M i)*K,mul_nonneg (mul_nonneg hP hprod) hK,?_⟩
  filter_upwards [hpoint,eventually_gt_atTop (1:ℝ)] with T hp hT
  intro σ hσ
  apply d02BalancedMoment_pointwise_error_bound hT
    (by linarith : (1/2:ℝ)+2*ε≤1) hK hP a M hM ρ hρM
  · intro i x hx
    by_contra hne
    exact (not_le_of_gt hx) (hs i (subset_tsupport (ρ i) hne)).2
  · exact hΦP
  · intro x hx
    by_contra hne
    exact hx (hΦs (subset_tsupport Φ hne))
  · intro t ht
    simpa only [show (1/2:ℝ)+2*ε-1=-1/2+2*ε by ring] using hp t ht σ hσ

/-- The proved complete pair error disappears in the actual denominator
normalization.  The only exponent condition is the profile-length saving. -/
theorem d02ZetaGaussianMomentError_normalized_tendsto {R ε : ℝ}
    (hR : 0≤R) (hε : 0<ε) (hε1 : ε≤1/4)
    (a : Fin 4 → ℝ) (hsaving : 1/2+2*ε+(∑ i,a i)/2<1)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ i,Continuous (ρ i))
    (hs : ∀ i,tsupport (ρ i)⊆Icc 0 (a i))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (σ : SecondMomentShifts) (hσ : ∀ j,‖σ j‖≤R) :
    Tendsto (fun T : ℝ => d02ZetaGaussianMomentError T σ ρ Φ /
      (T*(Real.log T)^9:ℂ)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := d02ZetaGaussianMomentError_uniform_bound
    hR hε hε1 a ρ hρ hs Φ hΦ hΦs
  let e : ℝ := 1/2+2*ε+(∑ i,a i)/2
  have hlim : Tendsto (fun T : ℝ => C*T^(e-1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by dsimp [e]; linarith : 0<1-e)).const_mul C
    simpa only [show -(1-e)=e-1 by ring,mul_zero] using h
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hlim
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hb hT hL
  have hTp : 0<T := zero_lt_one.trans hT
  have hLn : 0≤Real.log T := zero_le_one.trans hL
  have hpow : 1≤(Real.log T)^9 := one_le_pow₀ hL
  rw [norm_div,show (T*(Real.log T)^9:ℂ)=((T*(Real.log T)^9:ℝ):ℂ) by push_cast; rfl,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<T*(Real.log T)^9)]
  calc
    _ ≤ ‖d02ZetaGaussianMomentError T σ ρ Φ‖/T :=
      div_le_div_of_nonneg_left (norm_nonneg _) hTp (by nlinarith)
    _ ≤ (C*T^e)/T := div_le_div_of_nonneg_right (hb σ hσ) hTp.le
    _ = C*T^(e-1) := by rw [Real.rpow_sub hTp,Real.rpow_one]; ring

end
end Sechstmoment
