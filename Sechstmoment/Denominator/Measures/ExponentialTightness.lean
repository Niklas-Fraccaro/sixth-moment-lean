import Mathlib.MeasureTheory.Integral.Bochner.Set
import Sechstmoment.Denominator.Measures.DiagonalMeasureFinite
import Sechstmoment.Denominator.Measures.EuclideanLaplace

namespace Sechstmoment
open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal
noncomputable section
set_option maxHeartbeats 0

def d01OrthantSublevel (R : ℝ) : Set D01LogSpace :=
  d01PositiveOrthant ∩ {y | d01LogTotal y ≤ R}

theorem d01OrthantSublevel_isCompact (R : ℝ) : IsCompact (d01OrthantSublevel R) := by
  apply (isCompact_Icc : IsCompact (Icc (0 : D01LogSpace)
    ((fun _ => R), (fun _ => R)))).of_isClosed_subset
  · exact d01PositiveOrthant_isClosed.inter
      (isClosed_le d01LogTotal_continuous continuous_const)
  · intro y hy
    rcases hy with ⟨⟨hl, hr⟩, htotal⟩
    refine ⟨⟨hl, hr⟩, ?_⟩
    constructor
    · intro i
      have hsingle := Finset.single_le_sum (fun j _ => hl j) (Finset.mem_univ i)
      have hn : 0 ≤ ∑ j, y.2 j := Finset.sum_nonneg (fun j _ => hr j)
      change (∑ j, y.1 j) + ∑ j, y.2 j ≤ R at htotal
      linarith
    · intro j
      have hsingle := Finset.single_le_sum (fun i _ => hr i) (Finset.mem_univ j)
      have hn : 0 ≤ ∑ i, y.1 i := Finset.sum_nonneg (fun i _ => hl i)
      change (∑ i, y.1 i) + ∑ i, y.2 i ≤ R at htotal
      linarith

theorem d01DiagonalMeasure_half_exponential_integrable {L : ℝ} (hL : 0 < L) :
    Integrable (fun y => Real.exp (-d01LogTotal y / 2)) (d01DiagonalMeasure L) := by
  convert d01LaplaceWeight_integrable hL
    ((fun _ => (1/2 : ℝ)), (fun _ => (1/2 : ℝ)))
    (by intro i; norm_num) (by intro j; norm_num) using 1
  funext y
  unfold d01LaplaceWeight d01LogTotal
  congr 1
  simp only [← Finset.mul_sum]
  ring

theorem d01DiagonalMeasure_half_exponential_tendsto :
    Tendsto (fun L : ℝ => ∫ y, Real.exp (-d01LogTotal y / 2) ∂d01DiagonalMeasure L)
      atTop (𝓝 arithmeticFactor) := by
  convert d01DiagonalMeasure_laplace_tendsto
    ((fun _ => (1/2 : ℝ)), (fun _ => (1/2 : ℝ)))
    (by intro i; norm_num) (by intro j; norm_num) using 1
  · funext L
    apply integral_congr_ae
    filter_upwards [] with y
    unfold d01LaplaceWeight d01LogTotal
    congr 1
    simp only [← Finset.mul_sum]
    ring
  · norm_num

private theorem d01TailMajorant_integrable {L : ℝ} (hL : 0 < L) (R : ℝ) :
    Integrable (fun y => Real.exp ((d01LogTotal y - R) / 2))
      (d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal) := by
  rw [d01ExponentialTilt, integrable_withDensity_iff_integrable_smul'
    (by fun_prop) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  convert (d01DiagonalMeasure_half_exponential_integrable hL).const_mul
    (Real.exp (-R / 2)) using 1
  funext y
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [smul_eq_mul, ← Real.exp_add]
  congr 1
  ring

private theorem d01TailMajorant_integral (L R : ℝ) :
    (∫ y, Real.exp ((d01LogTotal y - R) / 2)
      ∂d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal) =
        Real.exp (-R / 2) *
          ∫ y, Real.exp (-d01LogTotal y / 2) ∂d01DiagonalMeasure L := by
  rw [d01ExponentialTilt, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [smul_eq_mul, ← Real.exp_add]
  congr 1
  ring

theorem d01DiagonalMeasure_exponential_tail_bound {L : ℝ} (hL : 0 < L) (R : ℝ) :
    (d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal).real
      {y | R < d01LogTotal y} ≤ Real.exp (-R / 2) *
        ∫ y, Real.exp (-d01LogTotal y / 2) ∂d01DiagonalMeasure L := by
  have hb := (d01TailMajorant_integrable hL R).measure_le_integral
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))
    (s := {y | R < d01LogTotal y}) (by
      intro y hy
      apply Real.one_le_exp_iff.mpr
      dsimp at hy ⊢
      linarith)
  rw [d01TailMajorant_integral] at hb
  have hnonneg : 0 ≤ Real.exp (-R / 2) *
      ∫ y, Real.exp (-d01LogTotal y / 2) ∂d01DiagonalMeasure L :=
    mul_nonneg (Real.exp_pos _).le (integral_nonneg (fun _ => (Real.exp_pos _).le))
  simpa only [measureReal_def, ENNReal.toReal_ofReal hnonneg] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hb

theorem d01DiagonalMeasure_uniform_exponential_tails :
    ∃ L₀ C : ℝ, 0 < L₀ ∧ 0 < C ∧ ∀ L : ℝ, L₀ ≤ L → ∀ R : ℝ,
      (d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal).real
        {y | R < d01LogTotal y} ≤ C * Real.exp (-R / 2) := by
  have he : ∀ᶠ L : ℝ in atTop,
      (∫ y, Real.exp (-d01LogTotal y / 2) ∂d01DiagonalMeasure L) <
        arithmeticFactor + 1 :=
    d01DiagonalMeasure_half_exponential_tendsto.eventually
      (eventually_lt_nhds (by linarith : arithmeticFactor < arithmeticFactor + 1))
  obtain ⟨A, hA⟩ := eventually_atTop.mp he
  refine ⟨max A 1, arithmeticFactor + 1, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  · linarith [arithmeticFactor_wellDefined.2]
  · intro L hL R
    have hLp : 0 < L := lt_of_lt_of_le
      (lt_of_lt_of_le zero_lt_one (le_max_right A 1)) hL
    apply (d01DiagonalMeasure_exponential_tail_bound hLp R).trans
    rw [mul_comm (arithmeticFactor + 1)]
    exact mul_le_mul_of_nonneg_left (hA L ((le_max_left A 1).trans hL)).le
      (Real.exp_pos _).le

theorem d01DiagonalMeasure_orthant_sublevel_complement {L : ℝ} (hL : 0 < L) (R : ℝ) :
    (d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal).real
      (d01OrthantSublevel R)ᶜ =
        (d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal).real
          {y | R < d01LogTotal y} := by
  apply measureReal_congr
  have ho : ∀ᵐ y ∂d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal,
      y ∈ d01PositiveOrthant := by
    exact (d01DiagonalMeasure_ae_orthant hL).filter_mono
      (withDensity_absolutelyContinuous (d01DiagonalMeasure L)
        (fun y => ENNReal.ofReal (Real.exp (-d01LogTotal y)))).ae_le
  filter_upwards [ho] with y hy
  simp [d01OrthantSublevel, hy]

theorem d01DiagonalMeasure_eventual_uniform_tightness :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ ε : ℝ, 0 < ε →
      ∃ K : Set D01LogSpace, IsCompact K ∧ ∀ L : ℝ, L₀ ≤ L →
        (d01ExponentialTilt (d01DiagonalMeasure L) d01LogTotal).real Kᶜ < ε := by
  obtain ⟨L₀, C, hL₀, hC, htail⟩ := d01DiagonalMeasure_uniform_exponential_tails
  refine ⟨L₀, hL₀, ?_⟩
  intro ε hε
  have ht : Tendsto (fun R : ℝ => C * Real.exp (-R / 2)) atTop (𝓝 0) := by
    have hr : Tendsto (fun R : ℝ => R / 2) atTop atTop :=
      tendsto_id.atTop_div_const (by norm_num)
    simpa only [mul_zero, Function.comp_def, neg_div] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hr).const_mul C
  obtain ⟨R, hR⟩ := (ht.eventually (eventually_lt_nhds hε)).exists
  refine ⟨d01OrthantSublevel R, d01OrthantSublevel_isCompact R, ?_⟩
  intro L hL
  rw [d01DiagonalMeasure_orthant_sublevel_complement (hL₀.trans_le hL)]
  exact (htail L hL R).trans_lt hR

end
end Sechstmoment
