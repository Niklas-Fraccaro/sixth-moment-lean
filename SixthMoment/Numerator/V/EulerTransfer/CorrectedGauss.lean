import SixthMoment.Arithmetic.Euler.FourL.Continuation
import SixthMoment.Numerator.V.Arithmetic.GaussMellinBound

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace SixthMoment.Source.NoDPGlobalLFactorization
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest NoDPGlobalConvolution
open Complex Real MeasureTheory Filter Set ZMod
open scoped Topology BigOperators Classical ContDiff
noncomputable section

def correctedGaussTransform (q : ℕ) [NeZero q] (d : ℕ) (s : Fin 4 → ℂ) (z : ℂ) : ℂ :=
  (q.totient:ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
    gaussSum χ⁻¹ stdAddChar * χ (-1) * shiftedContinuation χ d s z

theorem correctedGauss_norm_le (q : ℕ) [NeZero q] (d : ℕ) (s : Fin 4 → ℂ) (z : ℂ)
    (B : ℝ) (hB : ∀ χ : DirichletCharacter ℂ q, ‖eulerCorrection χ d s z‖ ≤ B) :
    ‖correctedGaussTransform q d s z‖ ≤ B * (q.totient:ℝ)⁻¹ * Real.sqrt q *
      ∑ χ : DirichletCharacter ℂ q, ∏ j : Fin 4, ‖χ.LFunction (z+s j)‖ := by
  have hsum : ‖∑ χ : DirichletCharacter ℂ q,
      gaussSum χ⁻¹ stdAddChar * χ (-1) * shiftedContinuation χ d s z‖ ≤
        B * Real.sqrt q * ∑ χ : DirichletCharacter ℂ q, ∏ j : Fin 4, ‖χ.LFunction (z+s j)‖ := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ _
    have hm : ‖χ (-1)‖ = 1 := by simpa using χ.unit_norm_eq_one (-1 : (ZMod q)ˣ)
    simp only [shiftedContinuation,norm_mul,norm_prod,hm,mul_one]
    calc
      _ ≤ Real.sqrt q * B * ∏ j : Fin 4, ‖χ.LFunction (z+s j)‖ := by
        have H := mul_le_mul (all_gaussSum_norm_le_sqrt q χ⁻¹) (hB χ)
          (norm_nonneg _) (Real.sqrt_nonneg _)
        have H' := mul_le_mul_of_nonneg_right H
          (show 0 ≤ ∏ j : Fin 4, ‖χ.LFunction (z+s j)‖ from
            Finset.prod_nonneg (fun _ _ => norm_nonneg _))
        simpa only [mul_assoc] using H'
      _ = _ := by ring
  rw [correctedGaussTransform,norm_mul,norm_inv,Complex.norm_natCast]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

theorem correctedGauss_bound (κ β ε : ℝ) (hκ : 0 < κ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, ∀ _ : NeZero q, ∀ d : ℕ, d ≠ 0 →
      ∀ s : Fin 4 → ℂ, (∀ j, ‖s j‖ ≤ min κ (β/2)) → ∀ z : ℂ, κ ≤ z.re →
      (∀ j, (z+s j).re ∈ Icc (1/2 : ℝ) (3/4)) → ∀ V : ℝ, 0 ≤ V →
      (∀ j, |(z+s j).im| ≤ V) →
        ‖correctedGaussTransform q d s z‖ ≤ C*(d:ℝ)^β*(q:ℝ)^(1/2+ε)*(1+V)^20 := by
  obtain ⟨E,hE,hcorr⟩ := eulerCorrection_subpower κ β hκ hβ
  obtain ⟨A,hA,hfour⟩ := allDirichlet_fourLProduct (ε := ε/2) (by linarith)
  obtain ⟨D,hD,hratio⟩ := modulus_totient_ratio_subpower (ε := ε/2) (by linarith)
  refine ⟨E*A*D,by positivity,?_⟩
  intro q hq d hd s hs z hz hsz V hV hVj
  have : NeZero q := hq
  have hqp : (0:ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hlocal := correctedGauss_norm_le q d s z (E*(d:ℝ)^β)
    (fun χ => hcorr q hq χ d hd s hs z hz)
  have he : Real.sqrt (q:ℝ)*(q:ℝ)^(1+ε/2) = (q:ℝ)*(q:ℝ)^(1/2+ε/2) := by
    calc
      _ = (q:ℝ)^((1/2:ℝ)+(1+ε/2)) := by rw [Real.sqrt_eq_rpow,← Real.rpow_add hqp]
      _ = (q:ℝ)^(1+(1/2+ε/2)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hqp,Real.rpow_one]
  have hp : (q:ℝ)^(ε/2)*(q:ℝ)^(1/2+ε/2) = (q:ℝ)^(1/2+ε) := by
    rw [← Real.rpow_add hqp]
    congr 1
    ring
  calc
    _ ≤ E*(d:ℝ)^β * (q.totient:ℝ)⁻¹ * Real.sqrt q *
        (A*(q:ℝ)^(1+ε/2)*(1+V)^20) := hlocal.trans (by gcongr; exact hfour q hq _ hsz V hV hVj)
    _ = E*(d:ℝ)^β*A*((q:ℝ)/(q.totient:ℝ))*(q:ℝ)^(1/2+ε/2)*(1+V)^20 := by
      calc
        _ = E*(d:ℝ)^β*A*(q.totient:ℝ)⁻¹ *
            (Real.sqrt (q:ℝ)*(q:ℝ)^(1+ε/2))*(1+V)^20 := by ring
        _ = _ := by rw [he]; ring
    _ ≤ E*(d:ℝ)^β*A*(D*(q:ℝ)^(ε/2))*(q:ℝ)^(1/2+ε/2)*(1+V)^20 := by
      gcongr
      exact hratio q hq
    _ = _ := by
      calc
        _ = E*A*D*(d:ℝ)^β*((q:ℝ)^(ε/2)*(q:ℝ)^(1/2+ε/2))*(1+V)^20 := by ring
        _ = _ := by rw [hp]

theorem correctedGauss_line_continuous (q : ℕ) [NeZero q] (d : ℕ) (s : Fin 4 → ℂ) (κ : ℝ)
    (H : ∀ j, κ+(s j).re ∈ Icc (1/2 : ℝ) (3/4)) :
    Continuous (fun v : ℝ => correctedGaussTransform q d s ((κ:ℂ)+(v:ℂ)*I)) := by
  unfold correctedGaussTransform
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro χ _
  apply Continuous.const_mul
  apply continuous_iff_continuousAt.mpr
  intro v
  apply (continuation_differentiableAt χ d s _ _).continuousAt.comp
    (by fun_prop)
  intro j
  left
  intro h
  have hr := congrArg Complex.re h
  simp only [add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero,one_re] at hr
  linarith [(H j).2]

end
end SixthMoment.Source.NoDPGlobalLFactorization
