import SixthMoment.Numerator.U.Replacement.VStar.TimeMellinEnvelope
import SixthMoment.Numerator.U.ZeroModes.GCDMellin.Front
import SixthMoment.Numerator.U.ZeroModes.Transforms.GammaCosStripGrowth

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeGCDArchKernel_full_height_envelope {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {cs : ℝ} (hcs : cs∈Icc (1/8:ℝ) (15/8)) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,0<T → ∀ σ : MomentShifts,∀ g a b : ℕ,0<g → 0<a → 0<b →
      ∀ x : ℝ,0<x → ∀ s : ℂ,s.re=cs →
      (1+|s.im|)^N*‖a03ZeroModeGCDArchKernel Φ T σ g a b x s‖≤
        C*(1+polarGaussianConstant T σ 1)*(x/T)^cs*
          a03ZeroModeRatioXEnvelope (T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ))) x := by
  obtain ⟨D,hD,hgamma⟩ := a03GammaCos_strip_polynomial_bound
  let n : ℕ := 2
  obtain ⟨E,hE,htime⟩ := SixthMoment.a03VStarSmoothedTimeMellin_full_height_envelope hΦ hSupp cs (N+n)
  refine ⟨D*E,by positivity,?_⟩
  intro T hT σ g a b hg ha hb x hx s hsc
  have hY := a03ZeroModeRatioPhysicalScale_pos hT hg ha hb
  have hYeq : a03ZeroModeRatioPhysicalScale T g a b=T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)) := by
    rw [a03ZeroModeRatioPhysicalScale_eq,Nat.cast_mul]
  rw [←hYeq]
  have hgammab := hgamma s (hsc ▸ hcs)
  change ‖Complex.Gamma s*Complex.cos (Real.pi*s/2)‖≤D*(1+|s.im|)^n at hgammab
  have htb := htime T σ _ x hY hx s hsc
  have he : a03ZeroModeGCDArchKernel Φ T σ g a b x s=
      ((x:ℂ)^s*(T:ℂ)^(-s))*(Complex.Gamma s*Complex.cos (Real.pi*s/2))*
        SixthMoment.a03VStarSmoothedTimeMellin Φ T σ (a03ZeroModeRatioPhysicalScale T g a b) x s := by
    rw [a03ZeroModeGCDArchKernel_eq_time hΦ hSupp hT σ hg ha hb hx (by rw [hsc]; exact lt_of_lt_of_le (by norm_num : (0:ℝ)<1/8) hcs.1)]
    unfold a03ZeroModeGCDArchTimeKernel SixthMoment.a03VStarSmoothedTimeMellin
      a03ZeroModeVStarTimeProfile a03ProfileProduct a03ZeroModeVStarTimeAmplitude
    rw [hYeq]
    ring
  have hpow : ‖(x:ℂ)^s*(T:ℂ)^(-s)‖=(x/T)^cs := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hx,Complex.norm_cpow_eq_rpow_re_of_pos hT,
      neg_re,hsc,Real.div_rpow hx.le hT.le,Real.rpow_neg hT.le]
    ring
  rw [he,norm_mul,norm_mul,hpow]
  have hCG := polarGaussianConstant_nonneg T σ 1
  calc
    _=(1+|s.im|)^N*((x/T)^cs*‖Complex.Gamma s*Complex.cos (Real.pi*s/2)‖)*
        ‖SixthMoment.a03VStarSmoothedTimeMellin Φ T σ (a03ZeroModeRatioPhysicalScale T g a b) x s‖ := by ring
    _≤(1+|s.im|)^N*((x/T)^cs*(D*(1+|s.im|)^n))*
        ‖SixthMoment.a03VStarSmoothedTimeMellin Φ T σ (a03ZeroModeRatioPhysicalScale T g a b) x s‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hgammab (by positivity)) (by positivity)) (norm_nonneg _)
    _=((x/T)^cs*D)*((1+|s.im|)^(N+n)*
        ‖SixthMoment.a03VStarSmoothedTimeMellin Φ T σ (a03ZeroModeRatioPhysicalScale T g a b) x s‖) := by
      rw [pow_add]
      ring
    _≤((x/T)^cs*D)*(E*(1+polarGaussianConstant T σ 1)*
        a03ZeroModeRatioXEnvelope (a03ZeroModeRatioPhysicalScale T g a b) x) :=
      mul_le_mul_of_nonneg_left htb (by positivity)
    _=_ := by ring

end
end SixthMoment.Source
