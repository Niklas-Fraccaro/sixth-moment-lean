import Sechstmoment.Denominator.Unbalanced.Expansion.Parameters
import Sechstmoment.Zeta.Bounds.LeftStrip
import Sechstmoment.Zeta.Gamma.PolynomialIntegrability

namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

theorem d04NegativeZetaArguments_small_components {T t η : ℝ}
    (σ : Fin 2 → ℂ) (hσ : ∀ j, ‖σ j/(Real.log T : ℂ)‖≤η) (j : Fin 2) :
    |(d04NegativeZetaArguments T t σ j).re-1/2|≤η ∧
      |(d04NegativeZetaArguments T t σ j).im+t|≤η := by
  have hre (j : Fin 2) := (Complex.abs_re_le_norm (σ j/(Real.log T : ℂ))).trans (hσ j)
  have him (j : Fin 2) := (Complex.abs_im_le_norm (σ j/(Real.log T : ℂ))).trans (hσ j)
  fin_cases j
  · change |(d04NegativeZetaArguments T t σ 0).re-1/2|≤η ∧
      |(d04NegativeZetaArguments T t σ 0).im+t|≤η
    have hr : (d04NegativeZetaArguments T t σ 0).re-1/2 =
        -(σ 0/(Real.log T : ℂ)).re := by
      simp [d04NegativeZetaArguments,criticalLinePoint]
      ring
    have hi : (d04NegativeZetaArguments T t σ 0).im+t =
        -(σ 0/(Real.log T : ℂ)).im := by
      simp [d04NegativeZetaArguments,criticalLinePoint]
      ring
    rw [hr,hi,abs_neg,abs_neg]
    exact ⟨hre 0,him 0⟩
  · change |(d04NegativeZetaArguments T t σ 1).re-1/2|≤η ∧
      |(d04NegativeZetaArguments T t σ 1).im+t|≤η
    have hr : (d04NegativeZetaArguments T t σ 1).re-1/2 =
        (σ 1/(Real.log T : ℂ)).re := by
      simp [d04NegativeZetaArguments,criticalLinePoint]
      ring
    have hi : (d04NegativeZetaArguments T t σ 1).im+t =
        (σ 1/(Real.log T : ℂ)).im := by
      simp [d04NegativeZetaArguments,criticalLinePoint]
    rw [hr,hi]
    exact ⟨hre 1,him 1⟩

theorem d04OneSidedLeft_zeta_bound {ε T t v C : ℝ}
    (hε : 0<ε) (hε4 : ε≤1/4) (hT : 512≤T) (ht : t∈Icc T (2*T))
    (hv : v∈Icc (-(T/4)) (T/4)) (σ : Fin 2 → ℂ)
    (hσ : ∀ j, ‖σ j/(Real.log T : ℂ)‖≤ε/8)
    (hC : 0≤C)
    (hζ : ∀ s : ℂ, -1≤s.re → s.re≤-(1/4:ℝ) →
      128≤|s.im| → ‖riemannZeta s‖≤C*(1+|s.im|)^(1/2-s.re))
    (j : Fin 2) :
    ‖riemannZeta (d04NegativeZetaArguments T t σ j+
      ((-1+ε/2:ℝ):ℂ)+(v:ℂ)*I)‖ ≤ (4*C)*T^(1-3*ε/8) := by
  let s := d04NegativeZetaArguments T t σ j
  let w : ℂ := s+((-1+ε/2:ℝ):ℂ)+(v:ℂ)*I
  have hs := d04NegativeZetaArguments_small_components (t := t) σ hσ j
  change |s.re-1/2|≤ε/8 ∧ |s.im+t|≤ε/8 at hs
  have hr := abs_le.mp hs.1
  have hi := abs_le.mp hs.2
  have hwr : w.re=s.re+(-1+ε/2) := by simp [w]
  have hwi : w.im=s.im+v := by simp [w]
  have hleft : -1≤w.re := by rw [hwr]; linarith
  have hright : w.re≤-(1/4:ℝ) := by rw [hwr]; linarith
  have hhigh : 128≤|w.im| := by
    have hn := neg_le_abs w.im
    have hwneg : w.im≤-128 := by
      rw [hwi]
      linarith [ht.1,hv.2]
    linarith
  have him : |w.im|≤3*T := by
    rw [hwi]
    apply abs_le.mpr
    constructor <;> linarith [ht.1,ht.2,hv.1,hv.2]
  have hbase : 1+|w.im|≤4*T := by linarith
  have hexp0 : 0≤1/2-w.re := by linarith
  have hexp : 1/2-w.re≤1-3*ε/8 := by rw [hwr]; linarith
  have hT0 : 0≤T := by linarith
  have hp : (1+|w.im|)^(1/2-w.re)≤4*T^(1-3*ε/8) := by
    calc
      _ ≤ (4*T)^(1/2-w.re) := Real.rpow_le_rpow (by positivity) hbase hexp0
      _ ≤ (4*T)^(1-3*ε/8) := Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
      _ = (4:ℝ)^(1-3*ε/8)*T^(1-3*ε/8) := Real.mul_rpow (by norm_num) hT0
      _ ≤ 4*T^(1-3*ε/8) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT0 _)
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4)
            (by linarith : 1-3*ε/8≤1)
  change ‖riemannZeta w‖≤_
  exact (hζ w hleft hright hhigh).trans
    ((mul_le_mul_of_nonneg_left hp hC).trans_eq (by ring))

theorem d04OneSidedLeft_integrand_bound {ε T t v C : ℝ}
    (hε : 0<ε) (hε4 : ε≤1/4) (hT : 512≤T) (ht : t∈Icc T (2*T))
    (hv : v∈Icc (-(T/4)) (T/4)) (σ : Fin 2 → ℂ)
    (hσ : ∀ j, ‖σ j/(Real.log T : ℂ)‖≤ε/8)
    (hC : 0≤C)
    (hζ : ∀ s : ℂ, -1≤s.re → s.re≤-(1/4:ℝ) →
      128≤|s.im| → ‖riemannZeta s‖≤C*(1+|s.im|)^(1/2-s.re)) :
    ‖d04OneSidedMellinIntegrand (T^3) (d04NegativeZetaArguments T t σ 0)
      (d04NegativeZetaArguments T t σ 1) (((-1+ε/2:ℝ):ℂ)+(v:ℂ)*I)‖ ≤
      ‖Complex.Gamma (((-1+ε/2:ℝ):ℂ)+(v:ℂ)*I)‖*
        ((4*C)^2*T^(-1+3*ε/4)) := by
  have hT0 : 0<T := by linarith
  have h₀ := d04OneSidedLeft_zeta_bound hε hε4 hT ht hv σ hσ hC hζ 0
  have h₁ := d04OneSidedLeft_zeta_bound hε hε4 hT ht hv σ hσ hC hζ 1
  have hp : ‖((T^3:ℝ):ℂ)^(((-1+ε/2:ℝ):ℂ)+(v:ℂ)*I)‖ =
      T^(3*(-1+ε/2)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<T^3)]
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]
    exact (Real.rpow_natCast_mul hT0.le 3 (-1+ε/2)).symm
  have hpow : T^(3*(-1+ε/2))*T^(1-3*ε/8)*T^(1-3*ε/8) =
      T^(-1+3*ε/4) := by
    rw [← Real.rpow_add hT0,← Real.rpow_add hT0]
    congr 1
    ring
  unfold d04OneSidedMellinIntegrand
  simp only [norm_mul]
  rw [hp]
  have hz₀ : ‖riemannZeta (d04NegativeZetaArguments T t σ 0+
      (((-1+ε/2:ℝ):ℂ)+(v:ℂ)*I))‖≤(4*C)*T^(1-3*ε/8) := by
    simpa only [add_assoc] using h₀
  have hz₁ : ‖riemannZeta (d04NegativeZetaArguments T t σ 1+
      (((-1+ε/2:ℝ):ℂ)+(v:ℂ)*I))‖≤(4*C)*T^(1-3*ε/8) := by
    simpa only [add_assoc] using h₁
  calc
    _ ≤ ‖Complex.Gamma (((-1+ε/2:ℝ):ℂ)+(v:ℂ)*I)‖*
        T^(3*(-1+ε/2))*((4*C)*T^(1-3*ε/8))*((4*C)*T^(1-3*ε/8)) := by
      gcongr
    _ = ‖Complex.Gamma (((-1+ε/2:ℝ):ℂ)+(v:ℂ)*I)‖*(4*C)^2*
        (T^(3*(-1+ε/2))*T^(1-3*ε/8)*T^(1-3*ε/8)) := by ring
    _ = _ := by rw [hpow]; ring

theorem d04OneSidedLeft_vertical_bound {ε R : ℝ}
    (hε : 0<ε) (hε4 : ε≤1/4) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ t∈Icc T (2*T), ∀ σ : Fin 2 → ℂ, (∀ j, ‖σ j‖≤R) →
        ‖d04OneSidedVerticalTruncated (T^3) (d04NegativeZetaArguments T t σ 0)
          (d04NegativeZetaArguments T t σ 1) (-1+ε/2) (T/4)‖ ≤ C*T^(-1+3*ε/4) := by
  obtain ⟨Z,hZ,hζ⟩ := d04RiemannZeta_sharp_left_strip (by norm_num : (0:ℝ)<1/4)
  have hc : -1<(-1+ε/2) := by linarith
  have hc2 : (-1+ε/2)≤2 := by linarith
  have hc0 : (-1+ε/2)≠0 := by linarith
  let g : ℝ → ℝ := fun v => ‖Complex.Gamma (((-1+ε/2:ℝ):ℂ)+(v:ℂ)*I)‖
  have hg : Integrable g := by
    simpa only [pow_zero,one_mul] using d04Gamma_vertical_polynomial_norm_integrable hc hc2 hc0 0
  let C : ℝ := (∫ v : ℝ, g v)*(4*Z)^2
  have hC : 0≤C := mul_nonneg (integral_nonneg (fun v => norm_nonneg _)) (sq_nonneg _)
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (512:ℝ),
    d04NormalizedShifts_uniform_eventually_small hR (by positivity : 0<ε/8)] with T hT hsmall
  intro t ht σ hσ
  have hT0 : 0<T := by linarith
  let K : ℝ := (4*Z)^2*T^(-1+3*ε/4)
  have hK : 0≤K := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hT0.le _)
  have hpoint (v : ℝ) (hv : v∈Ioc (-(T/4)) (T/4)) :
      ‖d04OneSidedMellinIntegrand (T^3) (d04NegativeZetaArguments T t σ 0)
        (d04NegativeZetaArguments T t σ 1) (((-1+ε/2:ℝ):ℂ)+(v:ℂ)*I)‖≤g v*K :=
    d04OneSidedLeft_integrand_bound hε hε4 hT ht ⟨hv.1.le,hv.2⟩ σ
      (hsmall.2 σ hσ) hZ hζ
  have hi : ‖d04OneSidedVerticalTruncated (T^3) (d04NegativeZetaArguments T t σ 0)
      (d04NegativeZetaArguments T t σ 1) (-1+ε/2) (T/4)‖≤
        ∫ v in Ioc (-(T/4)) (T/4), g v*K := by
    unfold d04OneSidedVerticalTruncated
    rw [intervalIntegral.integral_of_le (by linarith : -(T/4)≤T/4)]
    apply norm_integral_le_of_norm_le ((hg.mul_const K).restrict (s := Ioc (-(T/4)) (T/4)))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact hpoint v hv
  calc
    _ ≤ ∫ v in Ioc (-(T/4)) (T/4), g v*K := hi
    _ ≤ ∫ v : ℝ, g v*K := setIntegral_le_integral (hg.mul_const K)
      (ae_of_all _ (fun v => mul_nonneg (norm_nonneg _) hK))
    _ = C*T^(-1+3*ε/4) := by rw [integral_mul_const]; dsimp [C,K]; ring

theorem d04OneSidedLeft_vertical_bound_requested {ε R : ℝ}
    (hε : 0<ε) (hε4 : ε≤1/4) (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ t∈Icc T (2*T), ∀ σ : Fin 2 → ℂ, (∀ j, ‖σ j‖≤R) →
        ‖d04OneSidedVerticalTruncated (T^3) (d04NegativeZetaArguments T t σ 0)
          (d04NegativeZetaArguments T t σ 1) (-1+ε/2) (T/4)‖ ≤ C*T^(-1+ε) := by
  obtain ⟨C,hC,hbound⟩ := d04OneSidedLeft_vertical_bound hε hε4 hR
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with T hT hT1
  intro t ht σ hσ
  exact (hT t ht σ hσ).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)) hC)

end
end Sechstmoment
