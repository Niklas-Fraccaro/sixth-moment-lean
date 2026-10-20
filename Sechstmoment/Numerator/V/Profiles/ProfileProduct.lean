import Sechstmoment.Analysis.Harmonic.PolynomialProfile


namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set Polynomial
open scoped BigOperators Topology
noncomputable section

def divisorLogWeight (d e : ℕ) : ℝ := 1+Real.log d+Real.log e

theorem raw_triple_norm {η R B L : ℝ} {f : ℝ → ℂ}
    (hB : 0 ≤ B) (hf : ∀ x ∈ Icc 0 η, ‖f x‖ ≤ B)
    (hη : 0 ≤ η) (hR : 0 ≤ R) (hL : 1 ≤ L)
    (ν₁ ν₂ ν₃ : ℂ) (hν₁ : ‖ν₁‖ ≤ R) (hν₂ : ‖ν₂‖ ≤ R) (hν₃ : ‖ν₃‖ ≤ R)
    {d : ℕ} (hd : 1 ≤ d) :
    ‖rawIter L [ν₁,ν₂,ν₃] f (clippedTime η L d)‖ ≤
      (B*(kernelBound η R*(η+1))^3)*L^3 := by
  have hL0 : 0 < L := by linarith
  have hν : ∀ ν ∈ [ν₁,ν₂,ν₃], ‖ν‖ ≤ R := by
    intro ν hν
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hν
    rcases hν with rfl | rfl | rfl <;> assumption
  rw [rawIter_eq hL0.ne',show [ν₁,ν₂,ν₃].length = 3 from rfl,norm_mul,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
  apply (mul_le_mul_of_nonneg_left
    (discreteIter_norm hB hf hη hR hL [ν₁,ν₂,ν₃] hν (clippedTime_bounds hη hL0 hd).1)
    (by positivity : 0 ≤ L^3)).trans_eq
  simp only [List.length_cons,List.length_nil]
  ring

theorem profile_product_error {η R B D A E L : ℝ} {f g : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hg : RegularProfile η g A E)
    (hη : 0 ≤ η) (hR : 0 ≤ R) (hL : 1 ≤ L)
    (ν μ : Fin 3 → ℂ) (hν : ∀ j, ‖ν j‖ ≤ R) (hμ : ∀ j, ‖μ j‖ ≤ R)
    {d e : ℕ} (hd : 1 ≤ d) (he : 1 ≤ e) :
    let Cf := iterError η R B D 3+(iterBounds η R B D 3).2
    let Cg := iterError η R A E 3+(iterBounds η R A E 3).2
    let Ag := A*(kernelBound η R*(η+1))^3
    let Af := (iterBounds η R B D 3).1
    ‖rawIter L [ν 0,ν 1,ν 2] f (clippedTime η L d)*
        rawIter L [μ 0,μ 1,μ 2] g (clippedTime η L e) -
      (L:ℂ)^6*(continuousIter [ν 0,ν 1,ν 2] f η*
        continuousIter [μ 0,μ 1,μ 2] g η)‖ ≤
      (Cf*Ag+Af*Cg)*divisorLogWeight d e*L^5 := by
  dsimp only
  let S := rawIter L [ν 0,ν 1,ν 2] f (clippedTime η L d)
  let T := rawIter L [μ 0,μ 1,μ 2] g (clippedTime η L e)
  let I := continuousIter [ν 0,ν 1,ν 2] f η
  let J := continuousIter [μ 0,μ 1,μ 2] g η
  let Cf := iterError η R B D 3+(iterBounds η R B D 3).2
  let Cg := iterError η R A E 3+(iterBounds η R A E 3).2
  let Ag := A*(kernelBound η R*(η+1))^3
  let Af := (iterBounds η R B D 3).1
  have hL0 : 0 < L := by linarith
  have hE := (kernelBound_pos η R).le
  have hAg : 0 ≤ Ag := by dsimp [Ag]; have := hg.bound_nonneg; positivity
  have hAf : 0 ≤ Af := (iterBounds_nonneg (R := R) hη hf.bound_nonneg hf.lip_nonneg 3).1
  have hCf : 0 ≤ Cf := add_nonneg (iterError_nonneg hη hR hf.bound_nonneg hf.lip_nonneg 3)
    (iterBounds_nonneg (R := R) hη hf.bound_nonneg hf.lip_nonneg 3).2
  have hCg : 0 ≤ Cg := add_nonneg (iterError_nonneg hη hR hg.bound_nonneg hg.lip_nonneg 3)
    (iterBounds_nonneg (R := R) hη hg.bound_nonneg hg.lip_nonneg 3).2
  have hdlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  have helog : 0 ≤ Real.log e := Real.log_nonneg (by exact_mod_cast he)
  have hS := triple_simplex_error hf hη hR hL (ν 0) (ν 1) (ν 2) (hν 0) (hν 1) (hν 2) hd
  have hT := triple_simplex_error hg hη hR hL (μ 0) (μ 1) (μ 2) (hμ 0) (hμ 1) (hμ 2) he
  have hTnorm := raw_triple_norm hg.bound_nonneg hg.norm_le hη hR hL
    (μ 0) (μ 1) (μ 2) (hμ 0) (hμ 1) (hμ 2) he
  have hνs : ∀ z ∈ [ν 0,ν 1,ν 2], ‖z‖ ≤ R := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl <;> apply hν
  have hInorm : ‖(L:ℂ)^3*I‖ ≤ L^3*Af := by
    rw [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
    exact mul_le_mul_of_nonneg_left
      ((continuousIter_regular hf hη hR _ hνs).norm_le η ⟨hη,le_rfl⟩) (by positivity)
  have hid : S*T-(L:ℂ)^6*(I*J) = (S-(L:ℂ)^3*I)*T + (L:ℂ)^3*I*(T-(L:ℂ)^3*J) := by ring
  change ‖S*T-(L:ℂ)^6*(I*J)‖ ≤ (Cf*Ag+Af*Cg)*divisorLogWeight d e*L^5
  rw [hid]
  apply (norm_add_le _ _).trans
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (Cf*(1+Real.log d)*L^2)*(Ag*L^3) + (L^3*Af)*(Cg*(1+Real.log e)*L^2) :=
      add_le_add (mul_le_mul hS hTnorm (norm_nonneg _) (by positivity))
        (mul_le_mul hInorm hT (norm_nonneg _) (by positivity))
    _ = (Cf*Ag*(1+Real.log d)+Af*Cg*(1+Real.log e))*L^5 := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp only [divisorLogWeight]
      nlinarith [mul_nonneg (mul_nonneg hCf hAg) helog,mul_nonneg (mul_nonneg hAf hCg) hdlog]

end
end Sechstmoment.Source.NoDPHarmonic
