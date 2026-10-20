import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Sechstmoment.Analysis.Fourier.ProfileDecay

namespace Sechstmoment
open Complex Real MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology FourierTransform ContDiff
noncomputable section
set_option maxHeartbeats 0

def a03SmoothedCosine (Φ : ℝ→ℂ) (u : ℝ) : ℂ :=
  (profileLaplaceTransform Φ ((u:ℂ)*I)+profileLaplaceTransform Φ ((-u:ℂ)*I))/2

private theorem pureLaplace_integrable {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hK : HasCompactSupport Φ) (u : ℝ) :
    Integrable (fun t : ℝ => Complex.exp ((u:ℂ)*I*(t:ℂ))*Φ t) :=
  (by fun_prop : Continuous (fun t : ℝ => Complex.exp ((u:ℂ)*I*(t:ℂ))*Φ t)).integrable_of_hasCompactSupport hK.mul_left

theorem a03SmoothedCosine_eq_time_integral {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hK : HasCompactSupport Φ) (u : ℝ) :
    a03SmoothedCosine Φ u=∫ t : ℝ,(Real.cos (t*u):ℂ)*Φ t := by
  unfold a03SmoothedCosine profileLaplaceTransform
  have hn := pureLaplace_integrable hΦ hK (-u)
  simp only [Complex.ofReal_neg] at hn
  rw [←integral_add (pureLaplace_integrable hΦ hK u) hn,←integral_div]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Complex.ofReal_cos]
  unfold Complex.cos
  push_cast
  have he₁ : (t:ℂ)*(u:ℂ)*I=(u:ℂ)*I*(t:ℂ) := by ring
  have he₂ : -((t:ℂ)*(u:ℂ))*I=(-(u:ℂ))*I*(t:ℂ) := by ring
  rw [he₁,he₂]
  ring

theorem a03SmoothedCosine_continuous {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hK : HasCompactSupport Φ) : Continuous (a03SmoothedCosine Φ) := by
  have hFi : Integrable Φ := hΦ.integrable_of_hasCompactSupport hK
  have hF : Continuous (𝓕 Φ) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hFi
  have he : (fun u : ℝ => profileLaplaceTransform Φ ((u:ℂ)*I))=
      (fun u : ℝ => 𝓕 Φ (-u/(2*Real.pi))) := by
    funext u
    have hwt : profileExponentialWeight Φ 0=Φ := by
      funext t
      simp [profileExponentialWeight]
    simpa only [Complex.ofReal_zero,zero_add,hwt] using profileLaplaceTransform_eq_fourier Φ 0 u
  have hp : Continuous (fun u : ℝ => profileLaplaceTransform Φ ((u:ℂ)*I)) := by
    rw [he]
    exact hF.comp (by fun_prop)
  unfold a03SmoothedCosine
  convert (hp.add (hp.comp continuous_neg)).div_const 2 using 1
  funext u
  simp only [Pi.add_apply,Function.comp_apply,Complex.ofReal_neg]

theorem a03SmoothedCosine_frequency_power_bound {Φ : ℝ→ℂ}
    (hK : HasCompactSupport Φ) (hΦ : ContDiff ℝ ∞ Φ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ u : ℝ,|u|^N*‖a03SmoothedCosine Φ u‖≤C := by
  obtain ⟨C,hC,hb⟩ := a03_profile_frequency_power_bound hK hΦ N
  refine ⟨C,hC,?_⟩
  intro u
  have hp := hb u
  have hn := hb (-u)
  simp only [abs_neg,Complex.ofReal_neg] at hn
  unfold a03SmoothedCosine
  rw [norm_div,show ‖(2:ℂ)‖=2 by norm_num]
  have hsum := norm_add_le (profileLaplaceTransform Φ ((u:ℂ)*I))
    (profileLaplaceTransform Φ ((-u:ℂ)*I))
  calc
    _≤|u|^N*((‖profileLaplaceTransform Φ ((u:ℂ)*I)‖+
      ‖profileLaplaceTransform Φ ((-u:ℂ)*I)‖)/2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum (by norm_num)) (by positivity)
    _≤C := by nlinarith

theorem a03SmoothedCosine_mellinConvergent {Φ : ℝ→ℂ}
    (hK : HasCompactSupport Φ) (hΦ : ContDiff ℝ ∞ Φ) {s : ℂ} (hs : 0<s.re) :
    MellinConvergent (a03SmoothedCosine Φ) s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s.re
  obtain ⟨C,hC,hb⟩ := a03SmoothedCosine_frequency_power_bound hK hΦ N
  obtain ⟨D,_hD,hd⟩ := a03SmoothedCosine_frequency_power_bound hK hΦ 0
  have htop : a03SmoothedCosine Φ=O[atTop](fun u : ℝ => u^(-(N:ℝ))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨C,?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    rw [Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hu _),Real.rpow_neg hu.le,Real.rpow_natCast]
    have hp := hb u
    rw [abs_of_pos hu] at hp
    rw [←div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos hu N)).mpr (by simpa only [mul_comm] using hp)
  have hzero : a03SmoothedCosine Φ=O[𝓝[>] (0:ℝ)](fun u : ℝ => u^(-(0:ℝ))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨D,Eventually.of_forall (fun u => ?_)⟩
    simpa using hd u
  exact mellinConvergent_of_isBigO_rpow
    ((a03SmoothedCosine_continuous hΦ.continuous hK).locallyIntegrable.locallyIntegrableOn (Ioi 0))
    htop hN hzero hs

def a03CosineAbelScale (n : ℕ) : ℝ := 1/((n:ℝ)+1)

def a03DampedSmoothedCosine (Φ : ℝ→ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  (Real.exp (-a03CosineAbelScale n*u):ℂ)*a03SmoothedCosine Φ u

theorem a03CosineAbelScale_positive (n : ℕ) : 0<a03CosineAbelScale n := by
  unfold a03CosineAbelScale
  positivity

theorem a03CosineAbelScale_tendsto_zero : Tendsto a03CosineAbelScale atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  exact tendsto_atTop_mono (fun n : ℕ => by linarith) tendsto_natCast_atTop_atTop

theorem a03SmoothedCosine_abel_mellin_tendsto {Φ : ℝ→ℂ}
    (hK : HasCompactSupport Φ) (hΦ : ContDiff ℝ ∞ Φ) {s : ℂ} (hs : 0<s.re) :
    Tendsto (fun n : ℕ => mellin (a03DampedSmoothedCosine Φ n) s) atTop
      (𝓝 (mellin (a03SmoothedCosine Φ) s)) := by
  have hi := a03SmoothedCosine_mellinConvergent hK hΦ hs
  have hm : AEStronglyMeasurable (fun u : ℝ => (u:ℂ)^(s-1)*a03SmoothedCosine Φ u)
      (volume.restrict (Ioi 0)) := hi.aestronglyMeasurable
  have hmn (n : ℕ) : AEStronglyMeasurable (fun u : ℝ =>
      (u:ℂ)^(s-1)*a03DampedSmoothedCosine Φ n u) (volume.restrict (Ioi 0)) := by
    have hc : Continuous (fun u : ℝ => (Real.exp (-a03CosineAbelScale n*u):ℂ)) := by fun_prop
    convert hc.aestronglyMeasurable.mul hm using 1
    funext u
    simp only [a03DampedSmoothedCosine,Pi.mul_apply]
    ring
  have hb (n : ℕ) : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      ‖(u:ℂ)^(s-1)*a03DampedSmoothedCosine Φ n u‖≤
        ‖(u:ℂ)^(s-1)*a03SmoothedCosine Φ u‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    unfold a03DampedSmoothedCosine
    rw [show (u:ℂ)^(s-1)*((Real.exp (-a03CosineAbelScale n*u):ℂ)*a03SmoothedCosine Φ u)=
      (Real.exp (-a03CosineAbelScale n*u):ℂ)*((u:ℂ)^(s-1)*a03SmoothedCosine Φ u) by ring,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-a03CosineAbelScale n*u)≤1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (a03CosineAbelScale_positive n).le) hu.le)
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)
  have hlim : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      Tendsto (fun n : ℕ => (u:ℂ)^(s-1)*a03DampedSmoothedCosine Φ n u) atTop
        (𝓝 ((u:ℂ)^(s-1)*a03SmoothedCosine Φ u)) := by
    apply ae_of_all
    intro u
    have he : Tendsto (fun n : ℕ => (Real.exp (-a03CosineAbelScale n*u):ℂ)) atTop (𝓝 1) := by
      simpa only [neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one] using
        ((a03CosineAbelScale_tendsto_zero.neg.mul_const u).rexp).ofReal
    simpa only [a03DampedSmoothedCosine,one_mul] using
      (he.mul_const (a03SmoothedCosine Φ u)).const_mul ((u:ℂ)^(s-1))
  exact tendsto_integral_of_dominated_convergence _ hmn hi.norm hb hlim


theorem a03SmoothedCosine_mellin_tail_bound {Φ : ℝ→ℂ}
    (hK : HasCompactSupport Φ) (hΦ : ContDiff ℝ ∞ Φ) {s : ℂ} (hs : 0<s.re)
    (N : ℕ) (hN : s.re<(N:ℝ)) :
    ∃ C : ℝ,0≤C ∧ ∀ R : ℝ,0<R →
      (∫ u : ℝ in Ioi R,‖(u:ℂ)^(s-1)*a03SmoothedCosine Φ u‖)≤
        C*R^(s.re-(N:ℝ))/((N:ℝ)-s.re) := by
  obtain ⟨C,hC,hb⟩ := a03SmoothedCosine_frequency_power_bound hK hΦ N
  refine ⟨C,hC,?_⟩
  intro R hR
  have hi : IntegrableOn (fun u : ℝ => u^(s.re-1-(N:ℝ))) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hR
  have hi0 : Integrable (fun u : ℝ => ‖(u:ℂ)^(s-1)*a03SmoothedCosine Φ u‖) (volume.restrict (Ioi (0:ℝ))) := by
    simpa only [smul_eq_mul] using (a03SmoothedCosine_mellinConvergent hK hΦ hs).norm
  have hj : IntegrableOn (fun u : ℝ => ‖(u:ℂ)^(s-1)*a03SmoothedCosine Φ u‖) (Ioi R) :=
    hi0.mono_measure (Measure.restrict_mono_set _ (Ioi_subset_Ioi hR.le))
  have hmaj : ∀ᵐ u : ℝ ∂volume.restrict (Ioi R),
      ‖(u:ℂ)^(s-1)*a03SmoothedCosine Φ u‖≤C*u^(s.re-1-(N:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hup : 0<u := hR.trans hu
    have hpow := hb u
    rw [abs_of_pos hup] at hpow
    have hd : ‖a03SmoothedCosine Φ u‖≤C/(u^N) :=
      (le_div_iff₀ (pow_pos hup N)).mpr (by simpa only [mul_comm] using hpow)
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hup,Complex.sub_re,Complex.one_re]
    calc
      _≤u^(s.re-1)*(C/(u^N)) := mul_le_mul_of_nonneg_left hd (by positivity)
      _=C*u^(s.re-1-(N:ℝ)) := by
        have he : u^(s.re-1-(N:ℝ))=u^(s.re-1)/(u^N) := by
          rw [Real.rpow_sub hup,Real.rpow_natCast]
        rw [he]
        ring
  calc
    _≤∫ u : ℝ in Ioi R,C*u^(s.re-1-(N:ℝ)) := integral_mono_ae hj (hi.const_mul C) hmaj
    _=C*(-R^(s.re-1-(N:ℝ)+1)/(s.re-1-(N:ℝ)+1)) := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : s.re-1-(N:ℝ)< -1) hR]
    _=_ := by
      rw [show s.re-1-(N:ℝ)+1=s.re-(N:ℝ) by ring]
      have hd : -(R^(s.re-(N:ℝ)))/(s.re-(N:ℝ))=R^(s.re-(N:ℝ))/((N:ℝ)-s.re) := by
        rw [show (N:ℝ)-s.re=-(s.re-(N:ℝ)) by ring,div_neg,neg_div]
      rw [hd]
      ring

end
end Sechstmoment
