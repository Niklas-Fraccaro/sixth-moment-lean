import Sechstmoment.Numerator.V.Profiles.GammaMoment


namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set Polynomial NoDPGlobalRest
open scoped BigOperators Topology
noncomputable section

theorem gammaAt_sum_zero (i : Fin 4) :
    (∑' n : ℕ × ℕ, gammaAt i (fun _ => 0) n) = arithmeticConstant := by
  simpa only [restDirichletAt,restDirichlet,dirichletTerm,gammaAt,
    neg_zero,Complex.cpow_zero,mul_one] using restDirichletAt_zero i

theorem gammaAt_sum_error (i : Fin 4) (s : Fin 4 → ℂ) {ρ : ℝ}
    (hρ0 : 0 < ρ) (hρ : ρ < 1/4) (hs : ‖s‖ ≤ ρ/2) :
    ‖(∑' n : ℕ × ℕ, gammaAt i s n)-arithmeticConstant‖ ≤
      (2*uniformBound ρ/ρ)*‖s‖ := by
  have hs' : ∀ j, ‖reindexShifts i s j‖ ≤ ρ := by
    intro j
    exact (norm_le_pi_norm s _).trans (hs.trans (by linarith))
  have hsum : Summable (gammaAt i s) :=
    (gamma_absolute _ ρ hρ0.le hρ hs').of_norm
  have hzero : Summable (gammaAt i (fun _ => 0)) :=
    (gamma_absolute _ ρ hρ0.le hρ (by intro j; simp only [reindexShifts,Function.comp_apply,norm_zero]; positivity)).of_norm
  rw [← gammaAt_sum_zero i,← hsum.tsum_sub hzero]
  exact (norm_tsum_le_tsum_norm (hsum.sub hzero).norm).trans
    (gammaAt_lipschitz_zero i s ρ hρ0 hρ hs)

def productErrorConstant (η R B D A E : ℝ) : ℝ :=
  (iterError η R B D 3+(iterBounds η R B D 3).2)*
      (A*(kernelBound η R*(η+1))^3) +
    (iterBounds η R B D 3).1*(iterError η R A E 3+(iterBounds η R A E 3).2)

theorem productErrorConstant_nonneg {η R B D A E : ℝ}
    (hη : 0 ≤ η) (hR : 0 ≤ R) (hB : 0 ≤ B) (hD : 0 ≤ D) (hA : 0 ≤ A) (hE : 0 ≤ E) :
    0 ≤ productErrorConstant η R B D A E := by
  obtain ⟨hb,hd⟩ := iterBounds_nonneg (R := R) hη hB hD 3
  obtain ⟨ha,he⟩ := iterBounds_nonneg (R := R) hη hA hE 3
  have hf := iterError_nonneg hη hR hB hD 3
  have hg := iterError_nonneg hη hR hA hE 3
  have hk := (kernelBound_pos η R).le
  unfold productErrorConstant
  positivity

theorem gamma_profile_error {η R B D A E L ρ : ℝ} {f g : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hg : RegularProfile η g A E)
    (hη : 0 ≤ η) (hR : 0 ≤ R) (hL : 1 ≤ L)
    (i : Fin 4) (s : Fin 4 → ℂ) (hρ0 : 0 < ρ) (hρ : ρ < 1/4)
    (hs : ∀ j, ‖s j‖ ≤ ρ)
    (ν μ : Fin 3 → ℂ) (hν : ∀ j, ‖ν j‖ ≤ R) (hμ : ∀ j, ‖μ j‖ ≤ R) :
    let M := (L:ℂ)^6*(continuousIter [ν 0,ν 1,ν 2] f η*
      continuousIter [μ 0,μ 1,μ 2] g η)
    Summable (fun n : ℕ × ℕ => gammaAt i s n *
      (rawIter L [ν 0,ν 1,ν 2] f (clippedTime η L n.1)*
        rawIter L [μ 0,μ 1,μ 2] g (clippedTime η L n.2)-M)) ∧
    ‖∑' n : ℕ × ℕ, gammaAt i s n *
      (rawIter L [ν 0,ν 1,ν 2] f (clippedTime η L n.1)*
        rawIter L [μ 0,μ 1,μ 2] g (clippedTime η L n.2)-M)‖ ≤
      productErrorConstant η R B D A E*((1+1/ρ)*globalBound ρ)*L^5 := by
  dsimp only
  let C := productErrorConstant η R B D A E
  let M := (L:ℂ)^6*(continuousIter [ν 0,ν 1,ν 2] f η*continuousIter [μ 0,μ 1,μ 2] g η)
  let err := fun n : ℕ × ℕ => gammaAt i s n *
    (rawIter L [ν 0,ν 1,ν 2] f (clippedTime η L n.1)*
      rawIter L [μ 0,μ 1,μ 2] g (clippedTime η L n.2)-M)
  have hC : 0 ≤ C := productErrorConstant_nonneg hη hR hf.bound_nonneg hf.lip_nonneg
    hg.bound_nonneg hg.lip_nonneg
  have hL0 : 0 ≤ L := by linarith
  have hmajor : ∀ n : ℕ × ℕ, ‖err n‖ ≤ C*L^5*(‖gammaAt i s n‖*divisorLogWeight n.1 n.2) := by
    rintro ⟨d,e⟩
    by_cases hd : d = 0
    · subst d
      simp [err,gammaAt,gamma_zero_left]
    by_cases he : e = 0
    · subst e
      simp [err,gammaAt,gamma_zero_right]
    have h := profile_product_error hf hg hη hR hL ν μ hν hμ
      (Nat.one_le_iff_ne_zero.mpr hd) (Nat.one_le_iff_ne_zero.mpr he)
    change ‖gammaAt i s (d,e)*_‖ ≤ _
    rw [norm_mul]
    apply (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq
    dsimp only [C,productErrorConstant]
    ring
  have hsumm := (gammaAt_log_summable i s hρ0 hρ hs).mul_left (C*L^5)
  have hnorm : Summable (fun n => ‖err n‖) :=
    hsumm.of_nonneg_of_le (fun _ => norm_nonneg _) hmajor
  refine ⟨hnorm.of_norm,(norm_tsum_le_tsum_norm hnorm).trans ?_⟩
  calc
    _ ≤ ∑' n : ℕ × ℕ, C*L^5*(‖gammaAt i s n‖*divisorLogWeight n.1 n.2) :=
      hnorm.tsum_le_tsum hmajor hsumm
    _ = C*L^5*(∑' n : ℕ × ℕ, ‖gammaAt i s n‖*divisorLogWeight n.1 n.2) := tsum_mul_left
    _ ≤ C*L^5*((1+1/ρ)*globalBound ρ) :=
      mul_le_mul_of_nonneg_left (gammaAt_log_bound i s hρ0 hρ hs) (by positivity)
    _ = _ := by ring

def gammaProfileSum (η L : ℝ) (i : Fin 4) (s : Fin 4 → ℂ)
    (ν μ : Fin 3 → ℂ) (f g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ × ℕ, gammaAt i s n *
    (rawIter L [ν 0,ν 1,ν 2] f (clippedTime η L n.1)*
      rawIter L [μ 0,μ 1,μ 2] g (clippedTime η L n.2))

theorem gamma_profile_main_error {η R B D A E L ρ : ℝ} {f g : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hg : RegularProfile η g A E)
    (hη : 0 ≤ η) (hR : 0 ≤ R) (hL : 1 ≤ L)
    (i : Fin 4) (s : Fin 4 → ℂ) (hρ0 : 0 < ρ) (hρ : ρ < 1/4)
    (hs : ∀ j, ‖s j‖ ≤ ρ)
    (ν μ : Fin 3 → ℂ) (hν : ∀ j, ‖ν j‖ ≤ R) (hμ : ∀ j, ‖μ j‖ ≤ R) :
    ‖gammaProfileSum η L i s ν μ f g -
      (∑' n : ℕ × ℕ, gammaAt i s n)*
        ((L:ℂ)^6*(continuousIter [ν 0,ν 1,ν 2] f η*
          continuousIter [μ 0,μ 1,μ 2] g η))‖ ≤
      productErrorConstant η R B D A E*((1+1/ρ)*globalBound ρ)*L^5 := by
  let M := (L:ℂ)^6*(continuousIter [ν 0,ν 1,ν 2] f η*continuousIter [μ 0,μ 1,μ 2] g η)
  let F := fun n : ℕ × ℕ => rawIter L [ν 0,ν 1,ν 2] f (clippedTime η L n.1)*
    rawIter L [μ 0,μ 1,μ 2] g (clippedTime η L n.2)
  have hErr := gamma_profile_error hf hg hη hR hL i s hρ0 hρ hs ν μ hν hμ
  have hsum : Summable (gammaAt i s) :=
    (gamma_absolute _ ρ hρ0.le hρ (fun j => hs (Equiv.swap 0 i j))).of_norm
  have hmain := hsum.mul_right M
  have hid : gammaProfileSum η L i s ν μ f g =
      (∑' n, gammaAt i s n*(F n-M))+(∑' n, gammaAt i s n)*M := by
    rw [← tsum_mul_right,← hErr.1.tsum_add hmain]
    apply tsum_congr
    intro n
    ring
  rw [hid,add_sub_cancel_right]
  exact hErr.2

theorem gamma_profile_asymptotic {η R B D A E L ρ : ℝ} {f g : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hg : RegularProfile η g A E)
    (hη : 0 ≤ η) (hR : 0 ≤ R) (hL : 1 ≤ L)
    (i : Fin 4) (s : Fin 4 → ℂ) (hρ0 : 0 < ρ) (hρ : ρ < 1/4)
    (hs : ‖s‖ ≤ ρ/2) (hscale : ‖s‖ ≤ R/L)
    (ν μ : Fin 3 → ℂ) (hν : ∀ j, ‖ν j‖ ≤ R) (hμ : ∀ j, ‖μ j‖ ≤ R) :
    ‖gammaProfileSum η L i s ν μ f g - arithmeticConstant*
      ((L:ℂ)^6*(continuousIter [ν 0,ν 1,ν 2] f η*
        continuousIter [μ 0,μ 1,μ 2] g η))‖ ≤
      (productErrorConstant η R B D A E*((1+1/ρ)*globalBound ρ) +
        (2*uniformBound ρ/ρ)*R*(iterBounds η R B D 3).1*(iterBounds η R A E 3).1)*L^5 := by
  let M := (L:ℂ)^6*(continuousIter [ν 0,ν 1,ν 2] f η*continuousIter [μ 0,μ 1,μ 2] g η)
  let Z := ∑' n : ℕ × ℕ, gammaAt i s n
  let Af := (iterBounds η R B D 3).1
  let Ag := (iterBounds η R A E 3).1
  let K := 2*uniformBound ρ/ρ
  have hL0 : 0 < L := by linarith
  have hK : 0 ≤ K := by unfold K uniformBound; positivity
  have hAf : 0 ≤ Af := (iterBounds_nonneg (R := R) hη hf.bound_nonneg hf.lip_nonneg 3).1
  have hAg : 0 ≤ Ag := (iterBounds_nonneg (R := R) hη hg.bound_nonneg hg.lip_nonneg 3).1
  have hlist (v : Fin 3 → ℂ) (hv : ∀ j, ‖v j‖ ≤ R) : ∀ z ∈ [v 0,v 1,v 2], ‖z‖ ≤ R := by
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl | rfl <;> apply hv
  have hM : ‖M‖ ≤ L^6*(Af*Ag) := by
    rw [norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul
      ((continuousIter_regular hf hη hR _ (hlist ν hν)).norm_le η ⟨hη,le_rfl⟩)
      ((continuousIter_regular hg hη hR _ (hlist μ hμ)).norm_le η ⟨hη,le_rfl⟩)
      (norm_nonneg _) hAf
  have hZ : ‖Z-arithmeticConstant‖ ≤ K*(R/L) :=
    (gammaAt_sum_error i s hρ0 hρ hs).trans (mul_le_mul_of_nonneg_left hscale hK)
  have hmass : ‖(Z-arithmeticConstant)*M‖ ≤ K*R*Af*Ag*L^5 := by
    rw [norm_mul]
    apply (mul_le_mul hZ hM (norm_nonneg _) (by positivity)).trans_eq
    field_simp
  have hmain := gamma_profile_main_error hf hg hη hR hL i s hρ0 hρ
    (fun j => (norm_le_pi_norm s j).trans (hs.trans (by linarith))) ν μ hν hμ
  have hid : gammaProfileSum η L i s ν μ f g-arithmeticConstant*M =
      (gammaProfileSum η L i s ν μ f g-Z*M)+(Z-arithmeticConstant)*M := by ring
  change ‖gammaProfileSum η L i s ν μ f g-arithmeticConstant*M‖ ≤ _
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add hmain hmass).trans_eq (by ring))

end
end Sechstmoment.Source.NoDPHarmonic
