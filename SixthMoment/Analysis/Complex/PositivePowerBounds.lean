import SixthMoment.Analysis.Complex.PositivePowers


namespace SixthMoment.Source
open Complex Real Set
open scoped ContDiff
noncomputable section

theorem positive_unit_power_derivative_bound (j : ℕ)
    {c u : ℝ} (hc : c ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (1/2:ℝ) 2) :
    ‖iteratedDeriv j (fun y : ℝ => (y:ℂ)^(c:ℂ)) u‖ ≤
      2*((4:ℝ)*((j:ℝ)+1))^j := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hpow : u^c ≤ 2 := by
    by_cases hu1 : u ≤ 1
    · exact (Real.rpow_le_one hu0.le hu1 hc.1).trans (by norm_num)
    · exact (Real.rpow_le_self_of_one_le (le_of_lt (lt_of_not_ge hu1)) hc.2).trans hu.2
  have hinv : 1/u ≤ 2 := (div_le_iff₀ hu0).mpr (by linarith [hu.1])
  have hpower : u^(c-(j:ℝ)) ≤ 2*(2:ℝ)^j := by
    calc
      _ = u^c*(1/u)^j := by
        rw [Real.rpow_sub hu0,Real.rpow_natCast,div_pow,one_pow]
        ring
      _ ≤ _ := mul_le_mul hpow (pow_le_pow_left₀ (by positivity) hinv j)
        (by positivity) (by norm_num)
  have hcnorm : ‖(c:ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc.1]
    exact hc.2
  have hcoeff : ‖mellinFallingCoefficient j (c:ℂ)‖ ≤ ((j:ℝ)+1)^j*(2:ℝ)^j := by
    apply (mellinFallingCoefficient_norm_le j (c:ℂ)).trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith) j
  rw [positive_cpow_iteratedDeriv j (c:ℂ) hu0,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hu0,Complex.sub_re,
    Complex.ofReal_re,Complex.natCast_re]
  apply (mul_le_mul hcoeff hpower (by positivity) (by positivity)).trans_eq
  rw [mul_pow,show (4:ℝ) = 2*2 by norm_num,mul_pow]
  ring

end
end SixthMoment.Source
