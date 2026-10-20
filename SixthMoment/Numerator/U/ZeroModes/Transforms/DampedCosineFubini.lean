import SixthMoment.Numerator.U.ZeroModes.Transforms.ComplexLaplaceGamma
import SixthMoment.Numerator.U.ZeroModes.Transforms.SmoothedCosineMellin

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def a03DampedCosineTimeKernel (Φ : ℝ→ℂ) (s : ℂ) (ε u t : ℝ) : ℂ :=
  a03ComplexLaplaceGammaIntegrand s ε u*(Real.cos (t*u):ℂ)*Φ t

theorem a03DampedCosineTimeKernel_joint_integrable {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hK : HasCompactSupport Φ) {s : ℂ} (hs : 0<s.re) {ε : ℝ} (hε : 0<ε) :
    Integrable (Function.uncurry (a03DampedCosineTimeKernel Φ s ε))
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hU : Integrable (a03ComplexLaplaceGammaIntegrand s ε) (volume.restrict (Ioi 0)) :=
    a03ComplexLaplaceGamma_integrable hs (by simpa using hε)
  have hFi : Integrable Φ volume := hΦ.integrable_of_hasCompactSupport hK
  have hm : AEStronglyMeasurable (Function.uncurry (a03DampedCosineTimeKernel Φ s ε))
      ((volume.restrict (Ioi 0)).prod volume) := by
    unfold a03DampedCosineTimeKernel Function.uncurry
    exact (hU.aestronglyMeasurable.comp_fst.mul
      (by fun_prop : Continuous (fun p : ℝ×ℝ => (Real.cos (p.2*p.1):ℂ))).aestronglyMeasurable).mul
        hFi.aestronglyMeasurable.comp_snd
  apply (hU.norm.mul_prod hFi.norm).mono' hm
  apply ae_of_all
  intro p
  unfold Function.uncurry a03DampedCosineTimeKernel
  rw [norm_mul,norm_mul]
  have hcos : ‖(Real.cos (p.2*p.1):ℂ)‖≤1 := by
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  exact (mul_le_mul_of_nonneg_left hcos (norm_nonneg _) |>.trans_eq (mul_one _))
    |> fun h => mul_le_mul_of_nonneg_right h (norm_nonneg _)

theorem a03DampedSmoothedCosine_mellin_fubini {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hK : HasCompactSupport Φ) {s : ℂ} (hs : 0<s.re) (n : ℕ) :
    mellin (a03DampedSmoothedCosine Φ n) s=
      ∫ t : ℝ,∫ u : ℝ in Ioi 0,a03DampedCosineTimeKernel Φ s (a03CosineAbelScale n) u t := by
  rw [←integral_integral_swap (a03DampedCosineTimeKernel_joint_integrable hΦ hK hs (a03CosineAbelScale_positive n))]
  unfold mellin
  apply integral_congr_ae
  apply ae_of_all
  intro u
  dsimp only
  unfold a03DampedSmoothedCosine a03DampedCosineTimeKernel a03ComplexLaplaceGammaIntegrand
  simp only [mul_assoc,integral_const_mul]
  rw [a03SmoothedCosine_eq_time_integral hΦ hK u]
  simp only [smul_eq_mul]
  rw [Complex.ofReal_exp]
  congr 2
  push_cast
  ring


theorem a03DampedCosineTimeKernel_integral_eq {Φ : ℝ→ℂ} {s : ℂ}
    (hs : 0<s.re) {ε : ℝ} (hε : 0<ε) (t : ℝ) :
    (∫ u : ℝ in Ioi 0,a03DampedCosineTimeKernel Φ s ε u t)=
      Φ t*((((ε:ℂ)-(t:ℂ)*I)^(-s)+((ε:ℂ)+(t:ℂ)*I)^(-s))/2)*Complex.Gamma s := by
  let rMinus : ℂ := (ε:ℂ)-(t:ℂ)*I
  let rPlus : ℂ := (ε:ℂ)+(t:ℂ)*I
  have hm : 0<rMinus.re := by simpa [rMinus] using hε
  have hp : 0<rPlus.re := by simpa [rPlus] using hε
  have im : IntegrableOn (a03ComplexLaplaceGammaIntegrand s rMinus) (Ioi 0) :=
    a03ComplexLaplaceGamma_integrable hs hm
  have ip : IntegrableOn (a03ComplexLaplaceGammaIntegrand s rPlus) (Ioi 0) :=
    a03ComplexLaplaceGamma_integrable hs hp
  have vm : (∫u : ℝ in Ioi 0,a03ComplexLaplaceGammaIntegrand s rMinus u)=rMinus^(-s)*Complex.Gamma s :=
    a03ComplexLaplaceGamma_eq hs hm
  have vp : (∫u : ℝ in Ioi 0,a03ComplexLaplaceGammaIntegrand s rPlus u)=rPlus^(-s)*Complex.Gamma s :=
    a03ComplexLaplaceGamma_eq hs hp
  have he (u : ℝ) : a03DampedCosineTimeKernel Φ s ε u t=
      (a03ComplexLaplaceGammaIntegrand s rMinus u+a03ComplexLaplaceGammaIntegrand s rPlus u)/2*Φ t := by
    unfold a03DampedCosineTimeKernel a03ComplexLaplaceGammaIntegrand
    rw [Complex.ofReal_cos]
    unfold Complex.cos
    have em : -rMinus*(u:ℂ)=-(ε:ℂ)*(u:ℂ)+(t:ℂ)*I*(u:ℂ) := by dsimp [rMinus]; ring
    have ep : -rPlus*(u:ℂ)=-(ε:ℂ)*(u:ℂ)-(t:ℂ)*I*(u:ℂ) := by dsimp [rPlus]; ring
    rw [em,ep,Complex.exp_add,Complex.exp_sub]
    rw [show ((t*u:ℝ):ℂ)*I=(t:ℂ)*I*(u:ℂ) by push_cast; ring]
    rw [show -((t*u:ℝ):ℂ)*I=-((t:ℂ)*I*(u:ℂ)) by push_cast; ring,Complex.exp_neg]
    ring
  calc
    _=∫u : ℝ in Ioi 0,(a03ComplexLaplaceGammaIntegrand s rMinus u+a03ComplexLaplaceGammaIntegrand s rPlus u)/2*Φ t :=
      integral_congr_ae (ae_of_all _ he)
    _=((∫u : ℝ in Ioi 0,a03ComplexLaplaceGammaIntegrand s rMinus u)+
        (∫u : ℝ in Ioi 0,a03ComplexLaplaceGammaIntegrand s rPlus u))/2*Φ t := by
      rw [integral_mul_const,integral_div,integral_add im ip]
    _=_ := by rw [vm,vp]; dsimp [rMinus,rPlus]; ring

theorem a03DampedSmoothedCosine_mellin_eq_gamma {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hK : HasCompactSupport Φ) {s : ℂ} (hs : 0<s.re) (n : ℕ) :
    mellin (a03DampedSmoothedCosine Φ n) s=
      ∫ t : ℝ,Φ t*((((a03CosineAbelScale n:ℂ)-(t:ℂ)*I)^(-s)+
        ((a03CosineAbelScale n:ℂ)+(t:ℂ)*I)^(-s))/2)*Complex.Gamma s := by
  rw [a03DampedSmoothedCosine_mellin_fubini hΦ hK hs n]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => a03DampedCosineTimeKernel_integral_eq hs (a03CosineAbelScale_positive n) t)

end
end SixthMoment
