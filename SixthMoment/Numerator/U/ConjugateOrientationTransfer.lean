import SixthMoment.Numerator.U.TwistedMomentHolomorphy
import SixthMoment.Numerator.V.DP.DPPolydiscBoundary


namespace SixthMoment
open Complex Metric Set Filter Source
open scoped Topology ComplexConjugate
noncomputable section

set_option maxHeartbeats 2000000

def twistedConjugateSwapRadii (R : Fin 4 → ℝ) : Fin 4 → ℝ := ![R 2,R 3,R 0,R 1]

theorem twistedConjugateSwapShifts_involutive :
    Function.Involutive twistedConjugateSwapShifts := by
  intro σ
  ext j
  fin_cases j <;> simp [twistedConjugateSwapShifts]

theorem twistedConjugateSwapRadii_involutive :
    Function.Involutive twistedConjugateSwapRadii := by
  intro R
  ext j
  fin_cases j <;> simp [twistedConjugateSwapRadii]

theorem twistedConjugateSwapRadii_dpCauchy :
    twistedConjugateSwapRadii dpCauchyRadii = ![4,8,1,2] := by
  ext j
  fin_cases j <;> norm_num [twistedConjugateSwapRadii, dpCauchyRadii]

theorem twistedConjugateSwapShifts_mapsTo_polydisc (R : Fin 4 → ℝ) :
    MapsTo twistedConjugateSwapShifts (rectangularClosedPolydisc R)
      (rectangularClosedPolydisc (twistedConjugateSwapRadii R)) := by
  intro σ hσ j
  fin_cases j
  · simpa [twistedConjugateSwapShifts, twistedConjugateSwapRadii] using hσ 2
  · simpa [twistedConjugateSwapShifts, twistedConjugateSwapRadii] using hσ 3
  · simpa [twistedConjugateSwapShifts, twistedConjugateSwapRadii] using hσ 0
  · simpa [twistedConjugateSwapShifts, twistedConjugateSwapRadii] using hσ 1

theorem rawMomentShifts_conjugate_swap (T : ℝ) (σ : MomentShifts) :
    twistedConjugateSwapShifts (rawMomentShifts T σ) =
      rawMomentShifts T (twistedConjugateSwapShifts σ) := by
  ext j
  fin_cases j <;> simp [twistedConjugateSwapShifts, rawMomentShifts]

theorem normalized_twistedFourthMoment_conjugate_swap (T : ℝ) (σ : MomentShifts)
    (f g Φ : ℝ → ℝ) :
    conj (twistedFourthMoment T (rawMomentShifts T σ) f g Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9)) =
    twistedFourthMoment T (rawMomentShifts T (twistedConjugateSwapShifts σ)) g f Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9) := by
  rw [map_div₀, twistedFourthMoment_conj_swap, rawMomentShifts_conjugate_swap]
  congr 1
  simp

theorem normalized_twistedFourthMoment_uniform_polydisc_conjugate_swap
    (R : Fin 4 → ℝ) (f g Φ : ℝ → ℝ) (G : MomentShifts → ℂ)
    (hlimit : TendstoUniformlyOn
      (fun T σ => twistedFourthMoment T (rawMomentShifts T σ) f g Φ /
        ((T:ℂ)*(Real.log T:ℂ)^9))
      G atTop (rectangularClosedPolydisc R)) :
    TendstoUniformlyOn
      (fun T σ => twistedFourthMoment T (rawMomentShifts T σ) g f Φ /
        ((T:ℂ)*(Real.log T:ℂ)^9))
      (fun σ => conj (G (twistedConjugateSwapShifts σ))) atTop
      (rectangularClosedPolydisc (twistedConjugateSwapRadii R)) := by
  rw [Metric.tendstoUniformlyOn_iff] at hlimit ⊢
  intro ε hε
  filter_upwards [hlimit ε hε] with T hT σ hσ
  have hs : twistedConjugateSwapShifts σ ∈ rectangularClosedPolydisc R := by
    have hh := twistedConjugateSwapShifts_mapsTo_polydisc
      (twistedConjugateSwapRadii R) hσ
    simpa only [twistedConjugateSwapRadii_involutive R] using hh
  have hh := hT (twistedConjugateSwapShifts σ) hs
  have he : twistedFourthMoment T (rawMomentShifts T σ) g f Φ /
      ((T:ℂ)*(Real.log T:ℂ)^9) =
      conj (twistedFourthMoment T (rawMomentShifts T (twistedConjugateSwapShifts σ)) f g Φ /
        ((T:ℂ)*(Real.log T:ℂ)^9)) := by
    simpa only [twistedConjugateSwapShifts_involutive σ] using
      (normalized_twistedFourthMoment_conjugate_swap T (twistedConjugateSwapShifts σ)
        f g Φ).symm
  rw [he, dist_eq_norm, ← map_sub]
  simpa only [dist_eq_norm, norm_conj] using hh

end
end SixthMoment
