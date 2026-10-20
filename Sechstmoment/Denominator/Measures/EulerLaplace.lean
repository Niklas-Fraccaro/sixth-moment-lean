import Sechstmoment.Arithmetic.Euler.Shifted.ScaledLimit
import Sechstmoment.Numerator.U.Diagonal.DiagonalEulerSixIndices


namespace Sechstmoment

open Complex Filter
open scoped BigOperators Topology
open Classical

noncomputable section
set_option maxHeartbeats 0

def d01NormalizedDiagonalLaplace (L : ℝ) (a b : Fin 3 → ℂ) : ℂ :=
  (∑' x : DiagonalSixIndices,
    literalDiagonalSixTerm (fun i => a i / (L : ℂ))
      (fun i => b i / (L : ℂ)) x) / (L : ℂ)^9

theorem d01ScaledPowerArithmetic_eq_exp (L : ℝ) (a : ℂ) {n : ℕ} (hn : n ≠ 0) :
    shiftedPowerArithmetic (a/(L : ℂ)) n =
      Complex.exp (-a * ((Real.log (n : ℝ)/L : ℝ) : ℂ)) := by
  rw [shiftedPowerArithmetic_apply _ hn,
    Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
  rw [← Complex.natCast_log]
  congr 1
  simp only [Complex.ofReal_div]
  ring

theorem d01PositiveTriple_common_lower_bound (a b : Fin 3 → ℂ)
    (ha : ∀ i, 0 < (a i).re) (hb : ∀ i, 0 < (b i).re) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i, δ ≤ (a i).re) ∧ (∀ i, δ ≤ (b i).re) := by
  let s : Finset (Bool × Fin 3) := Finset.univ
  let f : Bool × Fin 3 → ℝ := fun x => if x.1 then (a x.2).re else (b x.2).re
  have hs : s.Nonempty := ⟨(true, 0), Finset.mem_univ _⟩
  refine ⟨s.inf' hs f, ?_, ?_, ?_⟩
  · apply (Finset.lt_inf'_iff hs).mpr
    rintro ⟨t,i⟩ _
    cases t
    · simpa only [f, Bool.false_eq_true, ↓reduceIte] using hb i
    · simpa only [f, ↓reduceIte] using ha i
  · intro i
    simpa only [f, ↓reduceIte] using (Finset.inf'_le (f := f) (Finset.mem_univ (true, i)))
  · intro i
    simpa only [f, Bool.false_eq_true, ↓reduceIte] using
      (Finset.inf'_le (f := f) (Finset.mem_univ (false, i)))

theorem d01ScaledDiagonalSixTerm_norm_summable {L : ℝ} (hL : 0 < L)
    (a b : Fin 3 → ℂ) (ha : ∀ i, 0 < (a i).re) (hb : ∀ i, 0 < (b i).re) :
    Summable (fun x : DiagonalSixIndices =>
      ‖literalDiagonalSixTerm (fun i => a i / (L : ℂ))
        (fun i => b i / (L : ℂ)) x‖) := by
  obtain ⟨δ, hδ, hda, hdb⟩ := d01PositiveTriple_common_lower_bound a b ha hb
  apply literalDiagonalSixTerm_norm_summable (δ := δ/L) (div_pos hδ hL)
  · intro i
    simpa only [Complex.div_ofReal_re] using div_le_div_of_nonneg_right (hda i) hL.le
  · intro i
    simpa only [Complex.div_ofReal_re] using div_le_div_of_nonneg_right (hdb i) hL.le

theorem d01NormalizedDiagonalLaplace_eq_euler {L : ℝ} (hL : 0 < L)
    (a b : Fin 3 → ℂ) (ha : ∀ i, 0 < (a i).re) (hb : ∀ i, 0 < (b i).re) :
    d01NormalizedDiagonalLaplace L a b =
      (∏ ij : Fin 3 × Fin 3,
        riemannZeta (1 + (a ij.1 + b ij.2)/(L : ℂ))/(L : ℂ)) *
          shiftedPolarEulerRest (fun i => a i/(L : ℂ)) (fun i => b i/(L : ℂ)) := by
  obtain ⟨δ, hδ, hda, hdb⟩ := d01PositiveTriple_common_lower_bound a b ha hb
  have hd := literalDiagonalSixTerm_eq_zetaProduct_mul_rest
    (δ := δ/L) (div_pos hδ hL)
    (a := fun i => a i/(L : ℂ)) (b := fun i => b i/(L : ℂ))
    (fun i => by
      simpa only [Complex.div_ofReal_re] using div_le_div_of_nonneg_right (hda i) hL.le)
    (fun i => by
      simpa only [Complex.div_ofReal_re] using div_le_div_of_nonneg_right (hdb i) hL.le)
  unfold d01NormalizedDiagonalLaplace
  rw [hd]
  have hadd (ij : Fin 3 × Fin 3) :
      1+a ij.1/(L : ℂ)+b ij.2/(L : ℂ) = 1+(a ij.1+b ij.2)/(L : ℂ) := by ring
  simp_rw [hadd]
  simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]
  ring

theorem d01NormalizedDiagonalLaplace_tendsto (a b : Fin 3 → ℂ)
    (ha : ∀ i, 0 < (a i).re) (hb : ∀ i, 0 < (b i).re) :
    Tendsto (fun L : ℝ => d01NormalizedDiagonalLaplace L a b) atTop
      (𝓝 ((arithmeticFactor : ℂ) * ∏ ij : Fin 3 × Fin 3, 1/(a ij.1+b ij.2))) := by
  have hp : Tendsto (fun L : ℝ => ∏ ij : Fin 3 × Fin 3,
      riemannZeta (1+(a ij.1+b ij.2)/(L : ℂ))/(L : ℂ)) atTop
        (𝓝 (∏ ij : Fin 3 × Fin 3, 1/(a ij.1+b ij.2))) := by
    apply tendsto_finsetProd
    intro ij _
    apply scaled_riemannZeta_tendsto
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.zero_re] at hr
    linarith [ha ij.1, hb ij.2]
  have he := shiftedPolarEulerRest_scaled_tendsto (a,b)
  have he' : Tendsto (fun L : ℝ => shiftedPolarEulerRest
      (fun i => a i/(L : ℂ)) (fun i => b i/(L : ℂ))) atTop
        (𝓝 (arithmeticFactor : ℂ)) := by
    simpa only [funext (scaledPolarShifts_fst _ _), funext (scaledPolarShifts_snd _ _)] using he
  have h := hp.mul he'
  rw [mul_comm] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  exact (d01NormalizedDiagonalLaplace_eq_euler hL a b ha hb).symm

end
end Sechstmoment
