import SixthMoment.Numerator.U.Replacement.VStar.PhysicalMellinBridge

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

private theorem physicalDenominator_inv_vertical_continuous (α : MomentShifts)
    (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (c : ℝ) :
    Continuous (fun v : ℝ => (a03ZeroModeRealQuadDenominator α ((c:ℂ)+(v:ℂ)*I) Q)⁻¹) := by
  have hd : Continuous (fun v : ℝ => a03ZeroModeRealQuadDenominator α ((c:ℂ)+(v:ℂ)*I) Q) := by
    unfold a03ZeroModeRealQuadDenominator
    apply continuous_finsetProd
    intro j _
    apply Continuous.const_cpow (by fun_prop)
    exact Or.inl (Complex.ofReal_ne_zero.mpr (hQ j).ne')
  apply hd.inv₀
  intro v
  unfold a03ZeroModeRealQuadDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (hQ j).ne'))

def a03PhysicalLeadingTimeKernel (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (Q : Fin 4→ℝ) (ξ c v t : ℝ) : ℂ :=
  Complex.exp (((-ξ:ℝ):ℂ)*I*(t:ℂ))*Φ t*
    a03PhysicalLeadingTimeAmplitude T σ α Q ((c:ℂ)+(v:ℂ)*I) t

private theorem physicalTimeKernel_logged (Φ : ℝ→ℂ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T)
    (σ α : MomentShifts) (Q : Fin 4→ℝ) (ξ c v t : ℝ) :
    a03PhysicalLeadingTimeKernel Φ T σ α Q ξ c v t=
      Complex.exp (((-ξ:ℝ):ℂ)*I*(t:ℂ))*Φ t*
        ((a03ZeroModeRealQuadDenominator α ((c:ℂ)+(v:ℂ)*I) Q)⁻¹*
          (polarPoleKiller T σ ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)*
            Complex.exp ((Real.log (T*t/2):ℂ)*(2*((c:ℂ)+(v:ℂ)*I)))*(Real.pi:ℂ)^(-2*((c:ℂ)+(v:ℂ)*I)))) := by
  by_cases ht : Φ t=0
  · simp [a03PhysicalLeadingTimeKernel,ht]
  · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
    have hp : 0<T*t/2 := by positivity
    unfold a03PhysicalLeadingTimeKernel a03PhysicalLeadingTimeAmplitude
    have he : (T*t/2:ℂ)=((T*t/2:ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),←Complex.ofReal_log hp.le]

theorem a03PhysicalLeadingTimeKernel_joint_integrable {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T c : ℝ} (hT : 0<T) (hc : 0<c)
    (σ α : MomentShifts) (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (ξ : ℝ) :
    Integrable (Function.uncurry (a03PhysicalLeadingTimeKernel Φ T σ α Q ξ c))
      (volume.prod volume) := by
  let B : ℝ := ‖(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹‖*
    polarGaussianConstant T σ c/c*(a03PhysicalQuadProduct Q)^(-c)*(2*T)^(2*c)
  have hP : 0<a03PhysicalQuadProduct Q := Finset.prod_pos (fun j _ => hQ j)
  have hCG := polarGaussianConstant_nonneg T σ c
  have hB : 0≤B := by dsimp [B]; positivity
  have hFK : HasCompactSupport Φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hSupp
  have hFi : Integrable Φ volume := hΦ.integrable_of_hasCompactSupport hFK
  have hmeas : AEStronglyMeasurable
      (Function.uncurry (a03PhysicalLeadingTimeKernel Φ T σ α Q ξ c)) (volume.prod volume) := by
    have hz : Continuous (fun p : ℝ×ℝ => (c:ℂ)+(p.1:ℂ)*I) := by fun_prop
    have hz0 (p : ℝ×ℝ) : (c:ℂ)+(p.1:ℂ)*I≠0 := by
      intro he
      have hr := congrArg Complex.re he
      simp at hr
      linarith
    have hD : Continuous (fun p : ℝ×ℝ => (a03ZeroModeRealQuadDenominator α ((c:ℂ)+(p.1:ℂ)*I) Q)⁻¹) :=
      (physicalDenominator_inv_vertical_continuous α Q hQ c).comp continuous_fst
    have hG := ((polarPoleKiller_differentiable T σ).continuous.comp hz).div hz hz0
    have hπ : Continuous (fun p : ℝ×ℝ => (Real.pi:ℂ)^(-2*((c:ℂ)+(p.1:ℂ)*I))) := by
      apply Continuous.const_cpow (by fun_prop)
      exact Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hlog : Measurable (fun p : ℝ×ℝ => (Real.log (T*p.2/2):ℂ)) := by fun_prop
    have hA : Measurable (fun p : ℝ×ℝ =>
        Complex.exp (((-ξ:ℝ):ℂ)*I*(p.2:ℂ))*Φ p.2*
          ((a03ZeroModeRealQuadDenominator α ((c:ℂ)+(p.1:ℂ)*I) Q)⁻¹*
            (polarPoleKiller T σ ((c:ℂ)+(p.1:ℂ)*I)/((c:ℂ)+(p.1:ℂ)*I)*
              Complex.exp ((Real.log (T*p.2/2):ℂ)*(2*((c:ℂ)+(p.1:ℂ)*I)))*(Real.pi:ℂ)^(-2*((c:ℂ)+(p.1:ℂ)*I))))) :=
      ((by fun_prop : Continuous (fun p : ℝ×ℝ => Complex.exp (((-ξ:ℝ):ℂ)*I*(p.2:ℂ)))).measurable.mul
        (hΦ.measurable.comp measurable_snd)).mul
          (hD.measurable.mul ((hG.measurable.mul (hlog.mul (hz.const_mul 2).measurable).cexp).mul hπ.measurable))
    convert hA.aestronglyMeasurable using 1
    funext p
    exact physicalTimeKernel_logged Φ hSupp hT σ α Q ξ c p.1 p.2
  apply (((gaussian_polynomial_half_integrable 48).mul_prod hFi.norm).const_mul B).mono' hmeas
  apply ae_of_all
  intro p
  by_cases ht : Φ p.2=0
  · simp only [a03PhysicalLeadingTimeKernel,Function.uncurry,ht,mul_zero,zero_mul,norm_zero]
    positivity
  · have hts := hSupp (subset_tsupport _ ht)
    have hb := a03PhysicalLeadingTimeAmplitude_gaussian_bound hT hc σ α Q hQ p.1 p.2 hts
    unfold Function.uncurry a03PhysicalLeadingTimeKernel
    rw [norm_mul,norm_mul,Complex.norm_exp]
    have hre : ((((-ξ:ℝ):ℂ)*I)*(p.2:ℂ)).re=0 := by simp
    rw [hre,Real.exp_zero,one_mul]
    calc
      _≤‖Φ p.2‖*(B*((1+|p.1|)^48*Real.exp (-(1/2)*p.1^2))) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _=_ := by ring

theorem a03PhysicalLeadingTimeKernel_vertical_time_eq_VStar
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts)
    (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (ξ : ℝ) :
    (1/(2*Real.pi):ℂ)*(∫v : ℝ,∫t : ℝ,a03PhysicalLeadingTimeKernel Φ T σ α Q ξ c v t)=
      (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*
        ∫t : ℝ,Complex.exp (((-ξ:ℝ):ℂ)*I*(t:ℂ))*Φ t*
          bblrVStar (polarPoleKiller T σ) (a03PhysicalQuadProduct Q/(T*t)^2) := by
  have hj := a03PhysicalLeadingTimeKernel_joint_integrable hΦ hSupp hT hc σ α Q hQ ξ
  rw [integral_integral_swap hj,←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  by_cases ht : Φ t=0
  · simp [a03PhysicalLeadingTimeKernel,ht]
  · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
    unfold a03PhysicalLeadingTimeKernel
    rw [integral_const_mul]
    have he := (a03PhysicalLeadingTimeAmplitude_vertical_eq_VStar hT htp hc σ α Q hQ).2
    unfold verticalIntegral at he
    calc
      _=(Complex.exp (((-ξ:ℝ):ℂ)*I*(t:ℂ))*Φ t)*
        ((1/(2*Real.pi):ℂ)*∫v : ℝ,a03PhysicalLeadingTimeAmplitude T σ α Q ((c:ℂ)+(v:ℂ)*I) t) := by ring
      _=_ := by rw [he]; ring

end
end SixthMoment
