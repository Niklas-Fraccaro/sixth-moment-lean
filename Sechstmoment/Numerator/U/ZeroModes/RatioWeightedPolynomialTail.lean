import Sechstmoment.Numerator.U.ZeroModes.RatioUnitTail

namespace Sechstmoment.Source
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

theorem a03ActualRatioPartition_uniform_weighted_polynomial_tail {κ γ A : ℝ}
    (hκ : 0<κ) (hγ : 0<γ) (hA : 0<A) (M : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ x : ℝ,A*T^γ≤x →
        ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (rawMomentShifts T σ)) x‖≤
          C*T^(-(M:ℝ))*x^(-1:ℝ) := by
  let e : ℝ := ((M:ℝ)+1)/γ
  let c : ℝ := 1+e
  have he : 0<e := by dsimp [e]; positivity
  have hc : 0<c := by dsimp [c]; positivity
  let J : ℝ := ∫ v : ℝ,(1+|v|)^4*Real.exp (-v^2)
  have hJ : 0≤J := integral_nonneg (fun _ => by positivity)
  let D : ℝ := (1/(2*Real.pi))*(Real.exp (c^2)*(c+1)^4*(1+1/κ^2)^2/c)*J
  have hD : 0≤D := by dsimp [D]; positivity
  let L : ℝ := ((4:ℕ).factorial:ℝ)/(1/2:ℝ)^4*Real.exp (1/2)
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨D*L*A^(-e),by positivity,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with T hT hlog
  intro σ hroot x hx
  have ht : 0<T := zero_lt_one.trans hT
  have hxpos : 0<x := (by positivity : 0<A*T^γ).trans_le hx
  have hg := a03ZeroModeRatioGaussianConstant_log_growth_radius hT hlog hκ σ hroot c
  have hb := a03ZeroModeRatioPartition_explicit_power_bound hc (rawMomentShifts T σ) hxpos
  have hp : (Real.log T)^4≤L*T^(1/2:ℝ) := by
    apply (pow_le_pow_left₀ (show 0≤Real.log T by linarith) (by linarith : Real.log T≤1+Real.log T) 4).trans
    exact Sechstmoment.logarithmic_power_le_rpow (by norm_num) hT.le 4
  have hxpow : x^(-e)≤A^(-e)*T^(-((M:ℝ)+1)) := by
    calc
      _≤(A*T^γ)^(-e) := Real.rpow_le_rpow_of_nonpos (by positivity) hx (neg_nonpos.mpr he.le)
      _=A^(-e)*T^(-((M:ℝ)+1)) := by
        rw [Real.mul_rpow hA.le (Real.rpow_nonneg ht.le _),←Real.rpow_mul ht.le]
        congr 1
        dsimp [e]
        field_simp
  have hxc : x^(-c)=x^(-e)*x^(-1:ℝ) := by
    rw [←Real.rpow_add hxpos]
    congr 1
    dsimp [c]
    ring
  calc
    _≤D*(Real.log T)^4*x^(-c) := by
      apply hb.trans
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hg hc.le)
            (show 0≤1/(2*Real.pi) by positivity)) hJ)
        (Real.rpow_nonneg hxpos.le (-c))
      convert hh using 1
      dsimp [D,J]
      ring
    _≤D*(L*T^(1/2:ℝ))*(A^(-e)*T^(-((M:ℝ)+1)))*x^(-1:ℝ) := by
      rw [hxc]
      have h₁ := mul_le_mul_of_nonneg_left hp hD
      have h₂ := mul_le_mul h₁ hxpow (Real.rpow_nonneg hxpos.le (-e))
        (mul_nonneg hD (mul_nonneg hL (Real.rpow_nonneg ht.le _)))
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right h₂
        (Real.rpow_nonneg hxpos.le (-1))
    _=(D*L*A^(-e))*T^(1/2-((M:ℝ)+1))*x^(-1:ℝ) := by
      rw [Real.rpow_sub ht,Real.rpow_neg ht.le]
      ring
    _≤_ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hxpos.le _)
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT.le (by linarith))
        (by positivity)

end
end Sechstmoment.Source
