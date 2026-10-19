import Sechstmoment.Numerator.V.Arithmetic.Additive.Series
import Sechstmoment.Numerator.V.Arithmetic.ShiftedMellinInsertion
import Sechstmoment.Numerator.V.EulerTransfer.DivisorRemainder

/-! The actual smoothed additive fourfold sum equals the full divisor and
Gauss-weighted Mellin expression on the absolute starting line. -/

namespace Sechstmoment.Source.NoDPGlobalLFactorization
open Complex Real Set MeasureTheory ZMod
open scoped BigOperators ContDiff
noncomputable section

theorem additive_fourAF_mellin_identity {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    (N : ℕ) (hN : N ≠ 0) (β : Fin 4 → ℂ) (c : ℝ)
    (hc : ∀ j, 1 < c+(β j).re) {x : ℝ} (hx : 0 < x) :
    (∑' m : ℕ, (fourAF β m*w ((m:ℝ)/x))*naturalAdditivePhase N m) =
      (1/(2*Real.pi):ℂ)*(∑ d : N.divisors, divisorMellinIntegral N hN d w c β x) := by
  classical
  let : NeZero N := ⟨hN⟩
  let a : ℕ → ℂ := fun m => fourAF β m*w ((m:ℝ)/x)
  have ha : Summable a := by
    apply summable_of_ne_finset_zero (s := Finset.range (⌈2*x⌉₊+1))
    intro m hm
    have hmNat : ⌈2*x⌉₊+1 ≤ m := by simpa only [Finset.mem_range,not_lt] using hm
    have hmReal : (⌈2*x⌉₊:ℝ)+1 ≤ m := by exact_mod_cast hmNat
    have hmx : 2*x < (m:ℝ) := by linarith [Nat.le_ceil (2*x)]
    have hz : w ((m:ℝ)/x) = 0 := by
      apply Function.notMem_support.mp
      intro hn
      have H := hws (subset_tsupport _ hn)
      have Hupper := (div_le_iff₀ hx).mp H.2
      linarith
    simp only [a,hz,mul_zero]
  change (∑' m : ℕ, a m*naturalAdditivePhase N m) = _
  rw [additive_series_character_decomposition_reindexed N a ha,
    ← Finset.sum_coe_sort N.divisors (fun d => additiveDirichletSeriesBlock N d a),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  let : NeZero (N/d.val) := divisorQuotientNeZero N hN d
  have hd : d.val ≠ 0 := NoDPGlobalConvolution.divisor_ne_zero d.property
  have hdpos : (0:ℝ) < d.val := by exact_mod_cast Nat.pos_of_ne_zero hd
  let y := x/(d.val:ℝ)
  have hy : 0 < y := div_pos hx hdpos
  let F : DirichletCharacter ℂ (N/d.val) → ℝ → ℂ := fun χ t =>
    mellin w ((c:ℂ)+(t:ℂ)*I)*(y:ℂ)^((c:ℂ)+(t:ℂ)*I)*
      shiftedContinuation χ d.val β ((c:ℂ)+(t:ℂ)*I)
  have hF (χ : DirichletCharacter ℂ (N/d.val)) : Integrable (F χ) :=
    shiftedContinuation_starting_line_integrable hw hws χ d.val hd β c hc hy
  have hseries (χ : DirichletCharacter ℂ (N/d.val)) :
      (∑' n : ℕ, a (d.val*n)*χ n) = (1/(2*Real.pi):ℂ)*(∫ t : ℝ, F χ t) := by
    let f : ℕ → ℂ := fun n => a (d.val*n)*χ n
    have hf0 : f 0 = 0 := by simp [f,a]
    have harg (n : ℕ+) : ((d.val*n:ℕ):ℝ)/x = (n:ℝ)/y := by
      dsimp only [y]
      push_cast
      field_simp [hdpos.ne',hx.ne']
    change (∑' n : ℕ, f n) = _
    calc
      _ = ∑' n : ℕ+, f n := (tsum_pnat_eq_tsum_of_eq_zero hf0).symm
      _ = ∑' n : ℕ+, (fourAF β (d.val*n)*χ n)*w ((n:ℝ)/y) := by
        apply tsum_congr
        intro n
        dsimp only [f,a]
        rw [harg]
        ring
      _ = _ := shifted_character_mellin_inversion hw hws χ d.val hd β c hc hy
  have hpoint (t : ℝ) : correctedMellinIntegrand (N/d.val) d.val w c β y t =
      ((N/d.val).totient:ℂ)⁻¹*
        ∑ χ : DirichletCharacter ℂ (N/d.val),
          (gaussSum χ⁻¹ stdAddChar*χ (-1))*F χ t := by
    dsimp only [correctedMellinIntegrand,correctedGaussTransform,F]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ _
    ring
  have hInt : divisorMellinIntegral N hN d w c β x =
      ((N/d.val).totient:ℂ)⁻¹*
        ∑ χ : DirichletCharacter ℂ (N/d.val),
          (gaussSum χ⁻¹ stdAddChar*χ (-1))*(∫ t : ℝ, F χ t) := by
    change (∫ t : ℝ, correctedMellinIntegrand (N/d.val) d.val w c β y t) = _
    simp_rw [hpoint]
    rw [integral_const_mul,integral_finsetSum _ (fun χ _ => (hF χ).const_mul _)]
    simp_rw [integral_const_mul]
  simp only [additiveDirichletSeriesBlock,dite_eq_right (NeZero.ne (N/d.val))]
  rw [hInt]
  simp_rw [hseries,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ _
  ring

end
end Sechstmoment.Source.NoDPGlobalLFactorization
