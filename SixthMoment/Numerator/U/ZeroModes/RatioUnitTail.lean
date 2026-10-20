import SixthMoment.Numerator.U.Separation.LogarithmicMellinWeights
import SixthMoment.Numerator.U.ZeroModes.ForwardMellin
import SixthMoment.Numerator.U.ZeroModes.Ratio.ContourBounds

namespace SixthMoment.Source
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem a03ZeroModeRatioGaussianConstant_log_growth_radius {T κ : ℝ}
    (hT : 1<T) (hL : 1≤Real.log T) (hκ : 0<κ) (σ : MomentShifts)
    (hρ : ∀ k : SixthMoment.PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) (R : ℝ) :
    a03ZeroModeRatioGaussianConstant (SixthMoment.rawMomentShifts T σ) R≤
      (Real.exp (R^2)*(R+1)^4*(1+1/κ^2)^2)*(Real.log T)^4 := by
  have hroot (j : Fin 2) :
      ‖((a03ZeroModeRatioRoot (SixthMoment.rawMomentShifts T σ) j)^2)⁻¹‖≤(Real.log T)^2/κ^2 := by
    fin_cases j
    · change ‖((a03ZeroModeRatioRoot (SixthMoment.rawMomentShifts T σ) 0)^2)⁻¹‖≤_
      rw [a03ZeroModeRatioRoot_zero_eq_pure]
      simpa using purePolarRoot_inverse_sq_norm hT hκ σ (2,(1,0)) (hρ (2,(1,0)))
    · change ‖((a03ZeroModeRatioRoot (SixthMoment.rawMomentShifts T σ) 1)^2)⁻¹‖≤_
      rw [a03ZeroModeRatioRoot_one_eq_pure]
      simpa using purePolarRoot_inverse_sq_norm hT hκ σ (2,(0,1)) (hρ (2,(0,1)))
  have hcost (j : Fin 2) :
      1+‖((a03ZeroModeRatioRoot (SixthMoment.rawMomentShifts T σ) j)^2)⁻¹‖≤
        (1+1/κ^2)*(Real.log T)^2 := by
    have h := hroot j
    rw [show (Real.log T)^2/κ^2=(1/κ^2)*(Real.log T)^2 by ring] at h
    have hs : 1≤(Real.log T)^2 := by nlinarith
    nlinarith
  unfold a03ZeroModeRatioGaussianConstant
  calc
    _≤(Real.exp (R^2)*(R+1)^4)*((1+1/κ^2)*(Real.log T)^2)*
      ((1+1/κ^2)*(Real.log T)^2) := by gcongr; exact hcost 0; exact hcost 1
    _=_ := by ring

theorem a03ZeroModeRatioPartition_explicit_power_bound {c : ℝ} (hc : 0<c)
    (α : MomentShifts) {x : ℝ} (hx : 0<x) :
    ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α) x‖≤
      (1/(2*Real.pi))*(a03ZeroModeRatioGaussianConstant α c/c)*
        (∫ v : ℝ,(1+|v|)^4*Real.exp (-v^2))*x^(-c) := by
  let F (v : ℝ) : ℂ := a03ZeroModeRatioWeight α ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)
  let P (v : ℝ) : ℝ := (1+|v|)^4*Real.exp (-v^2)
  have hF : Continuous F := by
    apply ((a03ZeroModeRatioWeight_differentiable α).continuous.comp
      (by fun_prop : Continuous (fun v : ℝ => (c:ℂ)+(v:ℂ)*I))).div (by fun_prop)
    intro v he
    have hr := congrArg Complex.re he
    simp at hr
    linarith
  have hP : Integrable P := by
    simpa [P] using SixthMoment.gaussianPolynomialExponential_integrable 4 0
  have hC : 0≤a03ZeroModeRatioGaussianConstant α c/c :=
    div_nonneg (a03ZeroModeRatioGaussianConstant_nonneg α c) hc.le
  have hb (v : ℝ) : ‖F v‖≤(a03ZeroModeRatioGaussianConstant α c/c)*P v := by
    have hz : c≤‖(c:ℂ)+(v:ℂ)*I‖ := by
      simpa using Complex.re_le_norm ((c:ℂ)+(v:ℂ)*I)
    have hg := a03ZeroModeRatioWeight_gaussian_bound α hc.le
      (z := (c:ℂ)+(v:ℂ)*I) (by simp [abs_of_pos hc])
    change ‖a03ZeroModeRatioWeight α ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)‖≤_
    rw [norm_div]
    calc
      _≤‖a03ZeroModeRatioWeight α ((c:ℂ)+(v:ℂ)*I)‖/c :=
        div_le_div_of_nonneg_left (norm_nonneg _) hc hz
      _≤_ := by
        have hh := div_le_div_of_nonneg_right hg hc.le
        simpa [P,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hi : Integrable F := (hP.const_mul _).mono' hF.aestronglyMeasurable (ae_of_all volume hb)
  have hint : (∫ v : ℝ,‖F v‖)≤(a03ZeroModeRatioGaussianConstant α c/c)*(∫ v : ℝ,P v) := by
    have hh := integral_mono hi.norm (hP.const_mul _) hb
    simpa only [integral_const_mul] using hh
  rw [a03ZeroModeRatioPartition_positive_contour hx hc (a03ZeroModeRatioWeight α) α
    (a03ZeroModeRatioWeight_admissible α)]
  unfold verticalIntegral
  rw [norm_mul]
  have hnorm : ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) := by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)).trans
  have he : (∫ v : ℝ,‖a03ZeroModeRatioKernel (a03ZeroModeRatioWeight α) x ((c:ℂ)+(v:ℂ)*I)‖)=
      (∫ v : ℝ,‖F v‖)*x^(-c) := by
    simp_rw [a03ZeroModeRatioKernel,norm_div,norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [neg_re,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]
    have hh (v : ℝ) : ‖a03ZeroModeRatioWeight α ((c:ℂ)+(v:ℂ)*I)‖*x^(-c)/‖(c:ℂ)+(v:ℂ)*I‖=
        ‖F v‖*x^(-c) := by dsimp [F]; rw [norm_div]; ring
    simp_rw [hh]
    rw [integral_mul_const]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hint (Real.rpow_nonneg hx.le (-c)))
    (show 0≤1/(2*Real.pi) by positivity)
  simpa only [P,mul_assoc] using hh

theorem a03ActualRatioPartition_uniform_polynomial_tail {κ γ A : ℝ}
    (hκ : 0<κ) (hγ : 0<γ) (hA : 0<A) (M : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ k : SixthMoment.PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ x : ℝ,A*T^γ≤x →
        ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (SixthMoment.rawMomentShifts T σ)) x‖≤
          C*T^(-(M:ℝ)) := by
  let c : ℝ := ((M:ℝ)+1)/γ
  have hc : 0<c := by dsimp [c]; positivity
  let J : ℝ := ∫ v : ℝ,(1+|v|)^4*Real.exp (-v^2)
  have hJ : 0≤J := integral_nonneg (fun _ => by positivity)
  let D : ℝ := (1/(2*Real.pi))*(Real.exp (c^2)*(c+1)^4*(1+1/κ^2)^2/c)*J
  have hD : 0≤D := by dsimp [D]; positivity
  let L : ℝ := ((4:ℕ).factorial:ℝ)/(1/2:ℝ)^4*Real.exp (1/2)
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨D*L*A^(-c),by positivity,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hT hlog
  intro σ hρ x hx
  have ht : 0<T := zero_lt_one.trans hT
  have hxpos : 0<x := (by positivity : 0<A*T^γ).trans_le hx
  have hg := a03ZeroModeRatioGaussianConstant_log_growth_radius hT hlog hκ σ hρ c
  have hb := a03ZeroModeRatioPartition_explicit_power_bound hc (SixthMoment.rawMomentShifts T σ) hxpos
  have hp : (Real.log T)^4≤L*T^(1/2:ℝ) := by
    apply (pow_le_pow_left₀ (show 0≤Real.log T by linarith) (by linarith : Real.log T≤1+Real.log T) 4).trans
    exact SixthMoment.logarithmic_power_le_rpow (by norm_num) hT.le 4
  have hxpow : x^(-c)≤A^(-c)*T^(-((M:ℝ)+1)) := by
    calc
      _≤(A*T^γ)^(-c) := Real.rpow_le_rpow_of_nonpos (by positivity) hx (neg_nonpos.mpr hc.le)
      _=A^(-c)*T^(-((M:ℝ)+1)) := by
        rw [Real.mul_rpow hA.le (Real.rpow_nonneg ht.le _),←Real.rpow_mul ht.le]
        congr 1
        dsimp [c]
        field_simp
  calc
    _≤D*(Real.log T)^4*x^(-c) := by
      apply hb.trans
      have hC : 0≤a03ZeroModeRatioGaussianConstant (SixthMoment.rawMomentShifts T σ) c :=
        a03ZeroModeRatioGaussianConstant_nonneg _ _
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hg hc.le)
            (show 0≤1/(2*Real.pi) by positivity)) hJ)
        (Real.rpow_nonneg hxpos.le (-c))
      convert hh using 1
      dsimp [D,J]
      ring
    _≤D*(L*T^(1/2:ℝ))*(A^(-c)*T^(-((M:ℝ)+1))) := by gcongr
    _=(D*L*A^(-c))*T^(1/2-((M:ℝ)+1)) := by
      rw [Real.rpow_sub ht]
      rw [Real.rpow_neg ht.le]
      ring
    _≤_ := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith))
        (by positivity)
end
end SixthMoment.Source
